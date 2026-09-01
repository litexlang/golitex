//! Named theorem compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: read the theorem's binder WD, proof-scope assumptions,
    /// ordered proof steps, conclusion checks, and outer store directly. This
    /// first binder-bearing tranche accepts ordinary object parameters with
    /// reviewed standard-set carriers. Other binder representations remain on
    /// the explicit compatibility path.
    pub(in super::super) fn compile_named_theorem_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefThmStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if verification.name != result.statement.name
            || verification.forall_fact.to_string() != result.statement.forall_fact.to_string()
            || verification.proof_steps.len() != result.statement.prove_process.len()
        {
            return Err("named theorem Result changed its declaration or proof-step order".into());
        }
        self.compile_named_forall_statement_result_to_lean_source(
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
        )
    }
}
