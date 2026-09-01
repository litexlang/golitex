//! Ordinary fact-goal proof bodies.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_ordinary_fact_goal_proof_body(
        &mut self,
        source_fact: &Fact,
        source_proof_step_count: usize,
        fact: &Fact,
        well_definedness: &SuccessVerifyFactWellDefinedResult,
        domain: &SuccessVerifyLocalProofScopeResult,
        proof_steps: &[StmtResult],
        conclusion_checks: &[StmtResult],
    ) -> Result<Option<CompiledOrdinaryFactGoalProofBody>, String> {
        if fact.to_string() != source_fact.to_string()
            || proof_steps.len() != source_proof_step_count
        {
            return Err("ordinary fact goal Result changed its target or proof-step order".into());
        }
        if !domain.assumption_infers.is_empty() || !domain.assumption_components.is_empty() {
            return Err("ordinary fact goal retained unexpected local assumptions".into());
        }
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(well_definedness, source_fact)?;
        }
        let goal_well_definedness =
            self.construct_well_definedness_to_lean_compilation_context(well_definedness)?;

        self.environment_stack.push_inherited_environment();
        self.environment_stack.well_definedness = Some(goal_well_definedness);
        let compilation = (|| {
            if let Some(recursive) = well_definedness.recursive.as_deref() {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    recursive,
                    &mut self.environment_stack,
                )?;
            }
            let mut local_proof_lines = Vec::with_capacity(proof_steps.len());
            for (proof_step_index, proof_step) in proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)
                    .map_err(|error| {
                        format!(
                            "ordinary fact goal proof step {} failed to compile: {error}",
                            proof_step_index + 1
                        )
                    })?
                else {
                    return Err(format!(
                        "ordinary fact goal proof step {} has no local compiler consumer: {:?}",
                        proof_step_index + 1,
                        proof_step
                    ));
                };
                local_proof_lines.extend(lines);
            }

            let [conclusion_check] = conclusion_checks else {
                return Err("ordinary fact goal must retain exactly one conclusion check".into());
            };
            let conclusion = conclusion_check
                .factual_success()
                .ok_or_else(|| "ordinary fact goal conclusion is not factual".to_string())?;
            if conclusion.fact().to_string() != source_fact.to_string() {
                return Err("ordinary fact goal conclusion changed its target".into());
            }
            if !conclusion.store.infers.is_empty() {
                validate_flattened_inferred_fact_ids_are_visible(
                    &conclusion.store.infers,
                    &self.environment_stack,
                    "ordinary fact goal conclusion",
                )?;
            }
            let Some(conclusion_proof) =
                self.construct_lean_proof_from_direct_fact_result(conclusion)?
            else {
                return Ok(None);
            };
            let proposition = render_fact(source_fact, &self.environment_stack)?;
            Ok(Some(CompiledOrdinaryFactGoalProofBody {
                local_proof_lines,
                proposition,
                conclusion_proof,
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }
}
