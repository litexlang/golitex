use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    /// Reuse a completed proof visible in the current environment chain.
    pub(crate) fn verify_atomic_fact_from_statement_memo(
        &self,
        fact: &AtomicFact,
    ) -> Option<StmtResult> {
        let key = fact.to_string();
        self.iter_environments_from_top().find_map(|environment| {
            environment
                .statement_atomic_fact_proofs
                .get(&key)
                .map(|source| {
                    SuccessFactStmtResult::new_with_statement_memo(
                        fact.clone().into(),
                        SuccessInferResult::new(),
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
        mut result: StmtResult,
    ) -> StmtResult {
        if result.is_unknown() {
            return result;
        }

        if let Some(success) = result.factual_success_mut() {
            if let Some(verification) = Rc::get_mut(&mut success.verification) {
                self.attach_known_fact_ids_to_verified_by(verification.proof_mut())
                    .expect("successful proof FactId attachment should not fail");
            }
        }

        let key = fact.to_string();
        let existing_source = {
            self.iter_environments_from_top()
                .find_map(|environment| environment.statement_atomic_fact_proofs.get(&key).cloned())
        };
        if existing_source.is_some() {
            return result;
        }

        let source = result
            .factual_success()
            .expect("successful atomic fact verification must return a factual result");
        let source = source.verification.clone();
        self.top_level_env()
            .statement_atomic_fact_proofs
            .insert(key, source.clone());

        result
    }

    // Compatibility shims for legacy, unreachable `Result<()>` verifier
    // implementations. Canonical WD evidence is returned recursively by the
    // matching `*_well_defined_result` functions; these functions retain no
    // Runtime or Environment state.
    pub(crate) fn begin_well_definedness_binder_scope(
        &mut self,
        _owner_object: &Obj,
    ) -> Result<Option<WellDefinedBinderScopeId>, RuntimeError> {
        Ok(None)
    }

    pub(crate) fn record_well_definedness_binder_parameter_group(
        &mut self,
        _scope_id: Option<WellDefinedBinderScopeId>,
        _parameter_group_index: usize,
        _group: &ParamGroupWithSet,
        _infer_result: &SuccessInferResult,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(crate) fn record_well_definedness_binder_domain(
        &mut self,
        _scope_id: Option<WellDefinedBinderScopeId>,
        _domain_index: usize,
        _expected: Fact,
        _infer_result: &SuccessInferResult,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(crate) fn record_well_definedness_set_builder_parameter(
        &mut self,
        _scope_id: Option<WellDefinedBinderScopeId>,
        _binding: &SymbolBinding,
        _expected: Fact,
        _infer_result: &SuccessInferResult,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(crate) fn record_well_definedness_set_builder_condition(
        &mut self,
        _scope_id: Option<WellDefinedBinderScopeId>,
        _condition_index: usize,
        _expected: Fact,
        _infer_result: &SuccessInferResult,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(crate) fn end_well_definedness_binder_scope(
        &mut self,
        _scope_id: Option<WellDefinedBinderScopeId>,
        _succeeded: bool,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    pub(crate) fn record_well_definedness_target_requirement(
        &mut self,
        _source_object: &Obj,
        _role: WellDefinednessRequirementRole,
        _result: StmtResult,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    /// End the statement-local lifetime on every active scope of the current execution frame.
    pub(crate) fn clear_statement_atomic_fact_proofs(&mut self) {
        let Some(frame) = self.execution_stack.last_mut() else {
            return;
        };
        let module_id = frame.module_id;
        let layer = frame.layer;
        for environment in frame.local_environment_stack.iter_mut() {
            environment.statement_atomic_fact_proofs.clear();
            environment.statement_well_defined_obj_proofs.clear();
        }

        let Some(module) = self.module_manager.module_mut(module_id) else {
            return;
        };
        module.main_environment.statement_atomic_fact_proofs.clear();
        module
            .main_environment
            .statement_well_defined_obj_proofs
            .clear();
        if let ExecutionLayer::File(file_id) = layer {
            if let Some(file) = module.file_mut(file_id) {
                file.environment.statement_atomic_fact_proofs.clear();
                file.environment.statement_well_defined_obj_proofs.clear();
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
        let first_source = direct_verification(&first);
        assert!(!matches!(
            first_source.proof(),
            SuccessFactProofResult::Reuse(_)
        ));
        assert!(runtime
            .top_level_env()
            .statement_atomic_fact_proofs
            .contains_key(&fact.to_string()));
        assert!(runtime
            .verify_fact_from_cache_using_display_string(&fact.clone().into())
            .is_none());

        let second = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("second verification should hit the statement memo");
        let second_source = reused_verification(&second);
        assert!(Rc::ptr_eq(&first_source, second_source));
        assert!(second.infer_result().is_empty());
        let output = display_stmt_exec_result_json(&runtime, &second, false);
        assert!(output.contains("number comparison"), "{output}");
        assert!(!output.contains("statement memo"), "{output}");

        runtime.clear_statement_atomic_fact_proofs();
        assert!(runtime
            .top_level_env()
            .statement_atomic_fact_proofs
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
            .statement_atomic_fact_proofs
            .contains_key(&fact.to_string()));

        runtime.clear_statement_atomic_fact_proofs();
        let stmt = parse_stmt(&mut runtime, "1 = 2");
        assert!(runtime.exec_stmt(&stmt).is_err());
        assert!(runtime
            .top_level_env()
            .statement_atomic_fact_proofs
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
                    .statement_atomic_fact_proofs
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
        let set_source = direct_verification(&first_set_result);
        let known_set_result = runtime
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&set_fact)
            .expect("known-only non-equality entry should consult the statement memo");
        assert!(Rc::ptr_eq(
            &set_source,
            reused_verification(&known_set_result)
        ));

        let equality = parse_atomic_fact(&mut runtime, "1 = 1");
        let first_equality_result = runtime
            .verify_atomic_fact(&equality, &UseContextVerifyState::new(0, false))
            .expect("reflexive equality should verify");
        let equality_source = direct_verification(&first_equality_result);
        let AtomicFact::EqualFact(equality_fact) = equality else {
            unreachable!()
        };
        let known_equality_result =
            runtime.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                &equality_fact.left,
                &equality_fact.right,
                equality_fact.line_file,
            ));
        assert!(Rc::ptr_eq(
            &equality_source,
            reused_verification(&known_equality_result)
        ));
    }

    #[test]
    fn next_statement_does_not_inherit_the_previous_memo_source() {
        let mut runtime = new_test_runtime();
        let fact = parse_atomic_fact(&mut runtime, "1 < 2");
        let first = runtime
            .verify_atomic_fact(&fact, &UseContextVerifyState::new(0, false))
            .expect("temporary proof should verify");
        let first_source = direct_verification(&first);

        let stmt = parse_stmt(&mut runtime, "1 < 2");
        let second = runtime
            .exec_stmt(&stmt)
            .expect("the next statement should verify independently");
        let second_source = direct_verification(&second);
        assert!(!Rc::ptr_eq(&first_source, &second_source));
        assert!(runtime
            .top_level_env()
            .statement_atomic_fact_proofs
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
            .statement_atomic_fact_proofs
            .is_empty());
        assert!(runtime
            .verify_fact_from_cache_using_display_string(&fact.clone().into())
            .is_some());
        let output = display_stmt_exec_result_json(&runtime, &result, false);
        assert!(output.contains("number comparison"), "{output}");
        assert!(!output.contains("statement memo"), "{output}");
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

    fn direct_verification(result: &StmtResult) -> Rc<SuccessVerifyFactResult> {
        let success = result
            .factual_success()
            .expect("atomic fact should be factual");
        success.verification.clone()
    }

    fn reused_verification(result: &StmtResult) -> &Rc<SuccessVerifyFactResult> {
        let success = result
            .factual_success()
            .expect("memoized atomic fact should be factual");
        let SuccessFactProofResult::Reuse(result) = success.proof() else {
            panic!("atomic success should retain its statement memo source");
        };
        &result.source
    }
}
