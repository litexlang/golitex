//! Strategy and setting definitions.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: a strategy definition has the same proof-producing forall
    /// body as a named theorem. The generated Lean declaration is the proved
    /// forall fact stored by the statement. The recursive Result owns the
    /// local WD, assumptions, proof steps, and conclusion checks.
    pub(in super::super) fn compile_strategy_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefStrategyStmtResult,
    ) -> Result<(), String> {
        let Some(verification) = &result.verification else {
            return Err(
                "StmtResultToLeanCompiler cannot compile a trusted-only strategy definition".into(),
            );
        };
        if verification.name != result.statement.name
            || verification.forall_fact.to_string() != result.statement.forall_fact.to_string()
            || verification.proof_steps.len() != result.statement.prove_process.len()
        {
            return Err("strategy Result changed its declaration or proof-step order".into());
        }
        if self.compile_named_forall_statement_result_to_lean_source(
            NamedForallStatementResultCompilationInput {
                name: &verification.name,
                forall_fact: &verification.forall_fact,
                well_definedness: &verification.well_definedness,
                proof_scope_assumption_infers: &verification.proof_scope.assumption_infers,
                proof_scope_assumption_components: &verification.proof_scope.assumption_components,
                proof_steps: &verification.proof_steps,
                conclusion_checks: verification.conclusion_checks.iter().collect(),
                outer_environment_effects: Some(&result.common.infers),
            },
        )? {
            Ok(())
        } else {
            Err("StmtResultToLeanCompiler does not support this strategy proof Result shape".into())
        }
    }

    /// `PassThrough`: a setting is a Litex elaboration declaration. Every use
    /// has already expanded to ordinary fresh binders and premise facts before
    /// execution produces later Results, so no setting binding belongs in the
    /// Lean-generation environment stack.
    pub(in super::super) fn compile_setting_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefSettingStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("setting definition unexpectedly published mathematical effects".into());
        }
        if result.statement.name.is_empty() {
            return Err("setting definition retained an empty source name".into());
        }
        Ok(())
    }
}
