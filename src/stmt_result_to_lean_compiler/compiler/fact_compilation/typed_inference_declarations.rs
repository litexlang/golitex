//! Typed inference top-level declarations with source constraints.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        result_layer: &str,
    ) -> Result<(), String> {
        if infers.rule_applications.is_empty() {
            if infers.store_fact_outputs.iter().all(|output| {
                output.inferred_facts.is_empty() && output.inferred_fact_ids.is_empty()
            }) {
                return Ok(());
            }
            return Err(format!(
                "{result_layer} retained inferred store effects without typed rule applications"
            ));
        }

        let compiled_steps = self.compile_typed_inference_results_in_current_compiler_environment(
            infers,
            allowed_sources,
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName,
            result_layer,
            None,
        )?;
        let mut preceding_steps: Vec<CompiledInferenceFactProofStep> = Vec::new();
        for step in compiled_steps {
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            let mut proof_lines = vec!["by".to_string()];
            proof_lines.extend(
                preceding_steps
                    .iter()
                    .map(CompiledInferenceFactProofStep::render_as_local_have_statement)
                    .map(|line| indent_lines(&line, 2)),
            );
            proof_lines.push(indent_lines(&format!("exact {}", step.proof_expression), 2));
            self.declarations.push(format!(
                "theorem {theorem_name} : {} := {}",
                step.proposition,
                proof_lines.join("\n")
            ));
            self.environment_stack
                .fact_names
                .insert(step.fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(step.fact_id, step.fact.clone());
            self.next_fact_name_index += 1;
            preceding_steps.push(step);
        }
        Ok(())
    }
}
