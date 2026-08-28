//! Typed inference replay as local have statements.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Final target-source rendering for callers that already own a Lean
    /// tactic block. The structured compilation above remains the only place
    /// that creates or installs an inferred fact.
    pub(in super::super) fn compile_typed_inference_results_as_local_have_statements(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        proof_lines: &mut Vec<String>,
        result_layer: &str,
    ) -> Result<(), String> {
        let compiled_steps = self.compile_typed_inference_results_in_current_compiler_environment(
            infers,
            allowed_sources,
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName,
            result_layer,
            None,
        )?;
        proof_lines.extend(
            compiled_steps
                .iter()
                .map(CompiledInferenceFactProofStep::render_as_local_have_statement),
        );
        Ok(())
    }

    /// Structured binders may reuse verified inference FactIds while changing
    /// only the Lean name of the exact source parameter. Replay those typed
    /// conclusions from the locally rebound assumptions instead of inheriting
    /// proof strings that mention the enclosing binder.
    pub(in super::super) fn compile_typed_inference_results_as_local_have_statements_replaying_visible(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        proof_lines: &mut Vec<String>,
        result_layer: &str,
        force_replay_visible_conclusions: &HashSet<FactId>,
    ) -> Result<(), String> {
        let compiled_steps = self.compile_typed_inference_results_in_current_compiler_environment(
            infers,
            allowed_sources,
            CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName,
            result_layer,
            Some(force_replay_visible_conclusions),
        )?;
        proof_lines.extend(
            compiled_steps
                .iter()
                .map(CompiledInferenceFactProofStep::render_as_local_have_statement),
        );
        Ok(())
    }
}
