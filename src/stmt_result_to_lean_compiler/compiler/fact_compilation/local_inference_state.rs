//! Local inference proof naming and retention.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Allocate one proof-local base name from the compiler-wide local-name
    /// counter. Source proof-step indices restart inside nested claims and
    /// forall bodies, so they are not valid Lean identifiers on their own:
    /// all emitted `have` declarations share one surrounding tactic scope.
    pub(in super::super) fn next_local_proof_step_base_name(&mut self) -> String {
        let name = format!(
            "__step{}_{}",
            self.next_fact_name_index, self.next_local_inference_name_index
        );
        self.next_local_inference_name_index += 1;
        name
    }

    pub(in super::super) fn next_local_inference_fact_proof_name(&mut self) -> String {
        let name = format!(
            "__infer{}_{}",
            self.next_fact_name_index, self.next_local_inference_name_index
        );
        self.next_local_inference_name_index += 1;
        name
    }

    pub(in super::super) fn retain_compiled_inference_fact_proof_step_in_current_environment(
        &mut self,
        compiled_steps: &mut Vec<CompiledInferenceFactProofStep>,
        step: CompiledInferenceFactProofStep,
        availability: CompiledInferenceFactAvailabilityInLeanEnvironment,
    ) {
        let lean_reference = match availability {
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName => {
                step.local_lean_name.clone()
            }
            CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression => {
                format!("({})", step.proof_expression)
            }
        };
        self.environment_stack
            .fact_names
            .insert(step.fact_id, lean_reference);
        self.environment_stack
            .fact_propositions
            .insert(step.fact_id, step.fact.clone());
        self.environment_stack
            .fact_lean_propositions
            .insert(step.fact_id, step.proposition.clone());
        compiled_steps.push(step);
    }
}
