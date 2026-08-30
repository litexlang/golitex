//! Local proof-step dispatch.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_stmt_result_as_local_proof_steps(
        &mut self,
        result: &StmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        if let StmtResult::Success(SuccessStmtResult::ProofBlock(
            SuccessProofBlockStmtResult::ClaimStmt(result),
        )) = result
        {
            return match &result.verification {
                Some(SuccessVerifyClaimResult::Forall(_)) => self
                    .compile_forall_claim_stmt_result_as_local_proof_steps(
                        result,
                        proof_step_index,
                    ),
                Some(SuccessVerifyClaimResult::Fact(_)) => self
                    .compile_fact_claim_stmt_result_as_local_proof_steps(result, proof_step_index),
                None => Ok(None),
            };
        }
        if let StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::ObtainObjFromExistFact(result),
        )) = result
        {
            return self.compile_obtain_obj_from_exist_fact_stmt_result_as_local_proof_steps(
                result,
                proof_step_index,
            );
        }
        if let StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::HaveObjEqualStmt(result),
        )) = result
        {
            return self
                .compile_have_obj_equal_stmt_result_as_local_proof_steps(result, proof_step_index);
        }
        if let StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::LetObjStmt(result),
        )) = result
        {
            return self.compile_let_obj_stmt_result_as_local_proof_steps(result, proof_step_index);
        }
        if let Some(factual) = result.factual_success() {
            if matches!(factual.proof(), SuccessFactProofResult::ForallProof(_)) {
                return self.compile_direct_forall_fact_result_as_local_proof_steps(factual);
            }
            return self
                .compile_fact_stmt_result_as_local_proof_step(factual, proof_step_index)
                .map(|line| line.map(|line| vec![line]));
        }
        if let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(result)) = result {
            let mut is_real_analysis_builtin = false;
            let (mut lines, conclusions) = if let Some(conclusions) =
                self.construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(result)?
            {
                (Vec::new(), conclusions)
            } else if let Some(compiled) =
                self.construct_local_real_analysis_builtin_theorem_application_proof(result)?
            {
                is_real_analysis_builtin = true;
                (compiled.local_prerequisite_lines, vec![compiled.conclusion])
            } else {
                return Ok(None);
            };
            let multiple_outputs = conclusions.len() > 1;
            lines.reserve(conclusions.len());
            let mut real_analysis_sources = Vec::new();
            for (output_index, conclusion) in conclusions.into_iter().enumerate() {
                let fact_id = conclusion.retained_fact_id.ok_or_else(|| {
                    format!(
                        "local release-thm conclusion `{}` has no retained FactId",
                        conclusion.fact
                    )
                })?;
                let name = if multiple_outputs {
                    format!("__step{proof_step_index}_{}", output_index + 1)
                } else {
                    format!("__step{proof_step_index}")
                };
                self.environment_stack
                    .fact_names
                    .insert(fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, conclusion.fact.clone());
                if is_real_analysis_builtin {
                    real_analysis_sources.push((fact_id, conclusion.fact.clone()));
                }
                lines.push(format!(
                    "have {name} : {} := by\n  exact {}",
                    conclusion.proposition, conclusion.proof_expression
                ));
            }
            if is_real_analysis_builtin {
                self.compile_typed_inference_results_as_local_have_statements(
                    &result.common.infers,
                    &real_analysis_sources,
                    &mut lines,
                    &format!(
                        "local real-analysis builtin theorem `{}` outer inference",
                        result.statement.name
                    ),
                )?;
            }
            return Ok(Some(lines));
        }
        if let StmtResult::Success(SuccessStmtResult::By(by_result)) = result {
            if let SuccessByStmtResult::ByThmStmt(result) = by_result {
                let Some(body) =
                    self.construct_lean_proof_from_by_theorem_selection_stmt_result(result)?
                else {
                    return Ok(None);
                };
                let name = format!("__step{proof_step_index}");
                self.environment_stack
                    .fact_names
                    .insert(body.retained_fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(body.retained_fact_id, body.fact);
                self.compile_defined_predicate_inference_results_in_current_environment(
                    &result.common.infers,
                    DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
                )?;
                validate_flattened_inferred_fact_ids_are_visible(
                    &result.common.infers,
                    &self.environment_stack,
                    "local by-thm selected parent fact",
                )?;
                return Ok(Some(vec![format!(
                    "have {name} : {} := by\n{}",
                    body.proposition,
                    indent_lines(&body.proof_lines.join("\n"), 2)
                )]));
            }
            if let SuccessByStmtResult::ByDefStmt(result) = by_result {
                return self.compile_by_definition_stmt_result_as_local_proof_steps(
                    result,
                    proof_step_index,
                );
            }
            if let SuccessByStmtResult::ByEnumerateFiniteSetStmt(result) = by_result {
                let Some(proof) =
                    self.construct_lean_proof_from_by_enumerate_finite_set_stmt_result(result)?
                else {
                    return Ok(None);
                };
                let fact_id = validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &proof.fact,
                    "local by-enumerate generated forall",
                )?;
                let name = format!("__step{proof_step_index}");
                self.environment_stack
                    .fact_names
                    .insert(fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, proof.fact);
                return Ok(Some(vec![format!(
                    "have {name} : {} := {}",
                    proof.proposition, proof.proof_expression
                )]));
            }
            if let SuccessByStmtResult::ByForStmt(result) = by_result {
                let Some(proof) = self.construct_lean_proof_from_by_for_stmt_result(result)? else {
                    return Ok(None);
                };
                let fact_id = validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &proof.fact,
                    "local by-for generated forall",
                )?;
                let name = format!("__step{proof_step_index}");
                self.environment_stack
                    .fact_names
                    .insert(fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, proof.fact);
                return Ok(Some(vec![format!(
                    "have {name} : {} := {}",
                    proof.proposition, proof.proof_expression
                )]));
            }
            if let SuccessByStmtResult::ByInducStmt(result) = by_result {
                let Some(proof) = self
                    .construct_lean_proof_from_structured_integer_induction_stmt_result(result)?
                else {
                    return Ok(None);
                };
                let fact_id = validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &proof.fact,
                    "local structured integer induction generated forall",
                )?;
                let name = format!("__step{proof_step_index}");
                self.environment_stack
                    .fact_names
                    .insert(fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, proof.fact);
                return Ok(Some(vec![format!(
                    "have {name} : {} := {}",
                    proof.proposition, proof.proof_expression
                )]));
            }
            let (proofs, effects) = match by_result {
                SuccessByStmtResult::ByCasesStmt(result) => (
                    self.construct_lean_proofs_from_by_cases_stmt_result(result)?,
                    &result.common.infers,
                ),
                SuccessByStmtResult::ByContraStmt(result) => (
                    self.construct_lean_proof_from_by_contra_stmt_result(result)?
                        .map(|proof| vec![proof]),
                    &result.common.infers,
                ),
                SuccessByStmtResult::ByExtensionStmt(result) => (
                    self.construct_lean_proof_from_by_extension_stmt_result(result)?
                        .map(|proof| vec![proof]),
                    &result.common.infers,
                ),
                _ => return Ok(None),
            };
            let Some(proofs) = proofs else {
                return Ok(None);
            };
            let fact_ids = validate_compiled_fact_proof_effects(
                effects,
                &proofs,
                &self.environment_stack,
                "local by-statement outputs",
            )?;
            let multiple_outputs = proofs.len() > 1;
            let mut lines = Vec::with_capacity(proofs.len());
            for (output_index, (proof, fact_id)) in proofs.into_iter().zip(fact_ids).enumerate() {
                let name = if multiple_outputs {
                    format!("__step{proof_step_index}_{}", output_index + 1)
                } else {
                    format!("__step{proof_step_index}")
                };
                if let Some(fact_id) = fact_id {
                    self.environment_stack
                        .fact_names
                        .insert(fact_id, name.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(fact_id, proof.fact);
                }
                lines.push(format!(
                    "have {name} : {} := by\n  exact {}",
                    proof.proposition, proof.proof_expression
                ));
            }
            return Ok(Some(lines));
        }
        if let StmtResult::Success(SuccessStmtResult::Witness(
            SuccessWitnessStmtResult::WitnessAtomicFact(result),
        )) = result
        {
            return self.compile_witness_atomic_fact_stmt_result_as_local_proof_steps(result);
        }
        if let StmtResult::Success(SuccessStmtResult::Witness(
            SuccessWitnessStmtResult::WitnessNonemptySet(result),
        )) = result
        {
            return self.compile_witness_nonempty_set_stmt_result_as_local_proof_steps(result);
        }
        let StmtResult::Success(SuccessStmtResult::Witness(
            SuccessWitnessStmtResult::WitnessExistFact(result),
        )) = result
        else {
            return Ok(None);
        };
        let Some(proof_body) =
            self.construct_lean_proof_from_witness_exist_fact_stmt_result(result)?
        else {
            return Ok(None);
        };
        let existential: Fact = result.statement.exist_fact_in_witness.clone().into();
        let fact_id = validate_single_fact_store_output(
            &result.common.infers,
            &existential,
            "local existential witness effect",
        )?;
        let name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, existential);
        Ok(Some(vec![format!(
            "have {name} : {} := by\n  exact {}",
            proof_body.proposition, proof_body.proof_expression
        )]))
    }
}
