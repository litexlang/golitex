use crate::prelude::*;
use std::rc::Rc;

use super::runtime::WellDefinednessObjectCaptureFrame;

impl Runtime {
    /// Reuse a completed proof visible in the current environment chain.
    pub(crate) fn verify_atomic_fact_from_statement_memo(
        &self,
        fact: &AtomicFact,
    ) -> Option<StmtResult> {
        let key = fact.to_string();
        self.iter_environments_from_top().find_map(|environment| {
            environment
                .statement_verified_atomic_facts
                .get(&key)
                .map(|source| {
                    FactualStmtSuccess::new_with_statement_memo(
                        fact.clone().into(),
                        InferResult::new(),
                        source.clone(),
                    )
                    .into()
                })
        })
    }

    /// Remember truth and its complete proof without committing the fact or running inference.
    pub(crate) fn remember_successful_atomic_fact_for_statement(
        &mut self,
        fact: &AtomicFact,
        result: StmtResult,
    ) -> StmtResult {
        if result.is_unknown() {
            return result;
        }

        let key = fact.to_string();
        let existing_source = {
            self.iter_environments_from_top().find_map(|environment| {
                environment
                    .statement_verified_atomic_facts
                    .get(&key)
                    .cloned()
            })
        };
        if let Some(source) = existing_source {
            let _ = self.record_well_definedness_proof_if_active(source);
            return result;
        }

        let success = result
            .into_factual_success()
            .expect("successful atomic fact verification must return a factual result");
        let infers = success.infers.clone();
        let source = Rc::new(success);
        self.top_level_env()
            .statement_verified_atomic_facts
            .insert(key, source.clone());
        let _ = self.record_well_definedness_proof_if_active(source.clone());

        FactualStmtSuccess::new_with_statement_memo(fact.clone().into(), infers, source).into()
    }

    fn record_well_definedness_proof_if_active(
        &mut self,
        proof: Rc<FactualStmtSuccess>,
    ) -> Option<WellDefinednessCertificateId> {
        if self.well_definedness_capture_depth == 0
            || !self.captures_litex_to_lean_well_definedness()
        {
            return None;
        }
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let Some(certificate) = self.well_definedness_capture_stack.last_mut() else {
            return None;
        };
        let certificate_id = if let Some(evidence) = certificate
            .facts
            .iter()
            .find(|evidence| Rc::ptr_eq(&evidence.proof, &proof))
        {
            evidence.certificate_id
        } else {
            let certificate_id =
                WellDefinednessCertificateId::new(certificate.facts.len() as u64 + 1);
            certificate.facts.push(WellDefinednessFactEvidence {
                certificate_id,
                role: WellDefinednessRequirementRole::SourceObjectRequirement,
                proof,
            });
            certificate_id
        };
        for frame in self.well_definedness_object_capture_stack.iter_mut() {
            if frame.statement_capture_depth == statement_capture_depth
                && !frame.fact_ids.contains(&certificate_id)
            {
                frame.fact_ids.push(certificate_id);
            }
        }
        Some(certificate_id)
    }

    pub(crate) fn begin_well_definedness_object_capture(&mut self, object: &Obj) {
        if !self.captures_litex_to_lean_well_definedness()
            || self.well_definedness_capture_stack.is_empty()
        {
            return;
        }
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let certificate = self
            .well_definedness_capture_stack
            .last()
            .expect("checked nonempty WD certificate stack");
        let active_count = self
            .well_definedness_object_capture_stack
            .iter()
            .filter(|frame| frame.statement_capture_depth == statement_capture_depth)
            .count();
        let occurrence_id = WellDefinednessObjectOccurrenceId::new(
            certificate.objects.len() as u64 + active_count as u64 + 1,
        );
        self.well_definedness_object_capture_stack
            .push(WellDefinednessObjectCaptureFrame::new(
                occurrence_id,
                object.clone(),
                statement_capture_depth,
            ));
    }

    pub(crate) fn end_well_definedness_object_capture(
        &mut self,
        succeeded: bool,
        intrinsic_result_set: Option<Obj>,
    ) {
        if !self.captures_litex_to_lean_well_definedness() {
            return;
        }
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let Some(frame) = self.well_definedness_object_capture_stack.pop() else {
            return;
        };
        if frame.statement_capture_depth != statement_capture_depth || !succeeded {
            return;
        }
        let Some(certificate) = self.well_definedness_capture_stack.last_mut() else {
            return;
        };
        certificate.objects.push(WellDefinednessObjectEvidence::new(
            frame.occurrence_id,
            frame.object,
            intrinsic_result_set,
            frame.fact_ids,
        ));
    }

    pub(crate) fn record_well_definedness_target_requirement(
        &mut self,
        source_object: &Obj,
        role: WellDefinednessRequirementRole,
        result: StmtResult,
    ) {
        if role == WellDefinednessRequirementRole::SourceObjectRequirement
            || !self.captures_litex_to_lean_well_definedness()
        {
            return;
        }
        let Some(success) = result.into_factual_success() else {
            return;
        };
        let expected_proposition = success.stmt.clone();
        let proof = if let VerifiedByResult::StatementMemo(proof) = &success.verified_by {
            proof.clone()
        } else {
            // A successful requirement need not have passed through the memo
            // cache. Preserve that exact verifier result rather than losing
            // the target proof reference or asking the Lean backend to search.
            Rc::new(success)
        };
        let Some(certificate_id) = self.record_well_definedness_proof_if_active(proof) else {
            return;
        };
        let statement_capture_depth = self.well_definedness_capture_stack.len();
        let source_key = obj_equality_key(source_object);
        let Some(object_occurrence_id) = self
            .well_definedness_object_capture_stack
            .iter()
            .rev()
            .find(|frame| {
                frame.statement_capture_depth == statement_capture_depth
                    && obj_equality_key(&frame.object) == source_key
            })
            .map(|frame| frame.occurrence_id)
        else {
            return;
        };
        let Some(certificate) = self.well_definedness_capture_stack.last_mut() else {
            return;
        };
        if certificate.target_requirements.iter().any(|requirement| {
            requirement.object_occurrence_id == object_occurrence_id
                && requirement.role == role
                && requirement.certificate_id == certificate_id
        }) {
            return;
        }
        certificate
            .target_requirements
            .push(WellDefinednessTargetRequirementEvidence::new(
                object_occurrence_id,
                source_object.clone(),
                role,
                certificate_id,
                expected_proposition,
            ));
    }

    /// End the statement-local lifetime on every active scope of the current execution frame.
    pub(crate) fn clear_statement_verified_atomic_facts(&mut self) {
        let Some(frame) = self.execution_stack.last_mut() else {
            return;
        };
        let module_id = frame.module_id;
        let layer = frame.layer;
        for environment in frame.local_environment_stack.iter_mut() {
            environment.statement_verified_atomic_facts.clear();
        }

        let Some(module) = self.module_manager.module_mut(module_id) else {
            return;
        };
        module
            .main_environment
            .statement_verified_atomic_facts
            .clear();
        if let ExecutionLayer::File(file_id) = layer {
            if let Some(file) = module.file_mut(file_id) {
                file.environment.statement_verified_atomic_facts.clear();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn successful_atomic_fact_is_shared_until_statement_memo_is_cleared() {
        let mut runtime = new_test_runtime();
        let fact = parse_atomic_fact(&mut runtime, "1 < 2");

        let first = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("first verification should run");
        let first_source = statement_memo_source(&first);
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .contains_key(&fact.to_string()));
        assert!(runtime
            .verify_fact_from_cache_using_display_string(&fact.clone().into())
            .is_none());

        let second = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("second verification should hit the statement memo");
        let second_source = statement_memo_source(&second);
        assert!(Rc::ptr_eq(first_source, second_source));
        assert!(second.infer_result().is_empty());
        let output = display_stmt_exec_result_json(&runtime, &second, false);
        assert!(output.contains("number comparison"), "{output}");
        assert!(!output.contains("statement memo"), "{output}");

        runtime.clear_statement_verified_atomic_facts();
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
    }

    #[test]
    fn unknown_atomic_fact_is_not_remembered() {
        let mut runtime = new_test_runtime();
        let fact = parse_atomic_fact(&mut runtime, "1 = 2");

        let result = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("unknown verification should not error");
        assert!(result.is_unknown());
        assert!(!runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .contains_key(&fact.to_string()));

        runtime.clear_statement_verified_atomic_facts();
        let stmt = parse_stmt(&mut runtime, "1 = 2");
        assert!(runtime.exec_stmt(&stmt).is_err());
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
    }

    #[test]
    fn local_environment_memo_is_visible_inward_and_discarded_outward() {
        let mut runtime = new_test_runtime();
        let parent_fact = parse_atomic_fact(&mut runtime, "1 < 2");
        let child_fact = parse_atomic_fact(&mut runtime, "2 < 3");
        runtime
            .verify_atomic_fact(&parent_fact, &UseContextVerifyState::new(0, false))
            .expect("parent fact should verify");

        runtime
            .run_in_local_env(|runtime| {
                assert!(runtime
                    .verify_atomic_fact_from_statement_memo(&parent_fact)
                    .is_some());
                runtime.verify_atomic_fact(&child_fact, &UseContextVerifyState::new(0, false))?;
                assert!(runtime
                    .top_level_env()
                    .statement_verified_atomic_facts
                    .contains_key(&child_fact.to_string()));
                Ok::<(), RuntimeError>(())
            })
            .expect("local verification should succeed");

        assert!(runtime
            .verify_atomic_fact_from_statement_memo(&parent_fact)
            .is_some());
        assert!(runtime
            .verify_atomic_fact_from_statement_memo(&child_fact)
            .is_none());
    }

    #[test]
    fn known_only_entry_points_reuse_statement_proofs() {
        let mut runtime = new_test_runtime();
        let set_fact = parse_atomic_fact(&mut runtime, "$is_set(R)");
        let first_set_result = runtime
            .verify_atomic_fact(&set_fact, &UseContextVerifyState::new(0, false))
            .expect("builtin set fact should verify");
        let set_source = statement_memo_source(&first_set_result).clone();
        let known_set_result = runtime
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&set_fact)
            .expect("known-only non-equality entry should consult the statement memo");
        assert!(Rc::ptr_eq(
            &set_source,
            statement_memo_source(&known_set_result)
        ));

        let equality = parse_atomic_fact(&mut runtime, "1 = 1");
        let first_equality_result = runtime
            .verify_atomic_fact(&equality, &UseContextVerifyState::new(0, false))
            .expect("reflexive equality should verify");
        let equality_source = statement_memo_source(&first_equality_result).clone();
        let AtomicFact::EqualFact(equality_fact) = equality else {
            unreachable!()
        };
        let known_equality_result = runtime.verify_objs_are_equal_by_known_equality(
            &equality_fact.left,
            &equality_fact.right,
            equality_fact.line_file,
        );
        assert!(Rc::ptr_eq(
            &equality_source,
            statement_memo_source(&known_equality_result)
        ));
    }

    #[test]
    fn next_statement_does_not_inherit_the_previous_memo_source() {
        let mut runtime = new_test_runtime();
        let fact = parse_atomic_fact(&mut runtime, "1 < 2");
        let first = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("temporary proof should verify");
        let first_source = statement_memo_source(&first).clone();

        let stmt = parse_stmt(&mut runtime, "1 < 2");
        let second = runtime
            .exec_stmt(&stmt)
            .expect("the next statement should verify independently");
        let second_source = statement_memo_source(&second);
        assert!(!Rc::ptr_eq(&first_source, second_source));
        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
    }

    #[test]
    fn exec_stmt_clears_temporary_successes_but_keeps_the_proof_evidence() {
        let mut runtime = new_test_runtime();
        let stmt = parse_stmt(&mut runtime, "1 < 2");
        let Stmt::Fact(Fact::AtomicFact(fact)) = &stmt else {
            unreachable!()
        };
        let result = runtime.exec_stmt(&stmt).expect("statement should verify");

        assert!(runtime
            .top_level_env()
            .statement_verified_atomic_facts
            .is_empty());
        assert!(runtime
            .verify_fact_from_cache_using_display_string(&fact.clone().into())
            .is_some());
        let output = display_stmt_exec_result_json(&runtime, &result, false);
        assert!(output.contains("number comparison"), "{output}");
        assert!(!output.contains("statement memo"), "{output}");
    }

    #[test]
    fn compile_to_lean_capture_retains_function_domain_well_definedness_proof() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(&mut runtime, "forall f fn(x R: x > 0) R:\n    f(2) = f(2)");

        let result = runtime
            .exec_stmt(&stmt)
            .expect("restricted-domain application should verify in Litex");
        let certificate = &result
            .factual_success()
            .expect("forall should return a factual success")
            .well_definedness;

        assert!(
            certificate
                .facts
                .iter()
                .any(|evidence| evidence.proof.stmt.to_string() == "2 > 0"),
            "captured facts: {:?}",
            certificate
                .facts
                .iter()
                .map(|evidence| evidence.proof.stmt.to_string())
                .collect::<Vec<_>>()
        );
        let requirement = certificate
            .target_requirements
            .iter()
            .find(|requirement| {
                requirement.expected_proposition.to_string() == "2 > 0"
                    && requirement.role
                        == WellDefinednessRequirementRole::FunctionDomain {
                            layer_index: 0,
                            domain_index: 0,
                        }
            })
            .expect("the application must retain its exact domain-proof reference");
        let object = certificate
            .objects
            .iter()
            .find(|object| object.occurrence_id == requirement.object_occurrence_id)
            .expect("the domain-proof reference must point to a checked object occurrence");
        assert!(object.object.to_string().ends_with("f(2)"));
        assert!(object.fact_ids.contains(&requirement.certificate_id));
    }

    #[test]
    fn compile_to_lean_capture_does_not_accept_a_boolean_obj_cache_without_proof_evidence() {
        let mut runtime = new_test_runtime();
        let warmup = parse_stmt(&mut runtime, "2 > 0");
        runtime
            .exec_stmt(&warmup)
            .expect("warmup fact should populate ordinary verifier caches");

        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(&mut runtime, "forall f fn(x R: x > 0) R:\n    f(2) = f(2)");
        let result = runtime
            .exec_stmt(&stmt)
            .expect("cached restricted-domain application should still verify");
        let certificate = &result.factual_success().unwrap().well_definedness;
        assert!(certificate
            .facts
            .iter()
            .any(|evidence| evidence.proof.stmt.to_string() == "2 > 0"));
    }

    #[test]
    fn compile_to_lean_capture_retains_have_fn_body_well_definedness_proofs() {
        let mut runtime = new_test_runtime();
        runtime.replace_litex_to_lean_well_definedness_mode(true);
        let stmt = parse_stmt(&mut runtime, "have fn reciprocal(x R: x != 0) R = 1 / x");

        let result = runtime
            .exec_stmt(&stmt)
            .expect("restricted function definition should verify in Litex");
        let success = result
            .non_factual_success()
            .expect("have-fn should return a non-factual success");
        let captured = success
            .well_definedness
            .facts
            .iter()
            .map(|evidence| evidence.proof.stmt.to_string())
            .collect::<Vec<_>>();

        assert!(
            captured.iter().any(|fact| fact.ends_with("x != 0")),
            "captured facts: {captured:?}"
        );
        assert_eq!(
            success.inside_results.len(),
            1,
            "have-fn must retain its checked return-membership result"
        );
        let verification = success
            .function_definition_verification
            .as_ref()
            .expect("have-fn must freeze its body-to-environment verification mapping");
        assert_eq!(verification.return_check_index, 0);
        assert_eq!(
            verification.assumption_infers.store_fact_outputs.len(),
            2,
            "the function parameter and domain premise must both be retained"
        );
        assert!(verification
            .assumption_infers
            .store_fact_outputs
            .iter()
            .all(|output| output.fact_id.is_some()));
        assert!(verification
            .function_membership
            .to_string()
            .contains("reciprocal $in fn"));
        assert!(verification
            .defining_equality
            .to_string()
            .contains("reciprocal = fn"));
        let return_check = success.inside_results[0]
            .factual_success()
            .expect("the retained return check must be factual");
        assert!(
            return_check.stmt.to_string().ends_with("x $in R"),
            "return check: {}",
            return_check.stmt
        );
        assert_eq!(
            success.infers.store_fact_outputs.len(),
            2,
            "stored function effects: {:?}",
            success.infers
        );
        assert!(
            success
                .infers
                .store_fact_outputs
                .iter()
                .all(|output| output.inferred_facts.is_empty()),
            "unexpected inferred function effects: {:?}",
            success.infers
        );
    }

    fn new_test_runtime() -> Runtime {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("statement_memo_test.lit");
        runtime
    }

    fn parse_atomic_fact(runtime: &mut Runtime, source: &str) -> AtomicFact {
        let stmt = parse_stmt(runtime, source);
        let Stmt::Fact(Fact::AtomicFact(fact)) = stmt else {
            panic!("expected an atomic fact: {source}");
        };
        fact
    }

    fn parse_stmt(runtime: &mut Runtime, source: &str) -> Stmt {
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(source, Rc::from("statement_memo_test.lit"))
            .expect("test statement should tokenize");
        assert_eq!(blocks.len(), 1);
        runtime
            .parse_stmt(&mut blocks[0])
            .expect("test statement should parse")
    }

    fn statement_memo_source(result: &StmtResult) -> &Rc<FactualStmtSuccess> {
        let success = result
            .factual_success()
            .expect("memoized atomic fact should be factual");
        let VerifiedByResult::StatementMemo(source) = &success.verified_by else {
            panic!("atomic success should retain its statement memo source");
        };
        source
    }
}
