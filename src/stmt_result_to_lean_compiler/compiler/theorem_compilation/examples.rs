//! Example statement compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: an `example` owns the same recursive proof body as a claim,
    /// but intentionally publishes neither a FactId nor an outer environment
    /// effect.
    pub(in super::super) fn compile_example_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessExampleStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if matches!(verification.fact, Fact::ForallFact(_)) {
            return Ok(false);
        }
        if !result.common.infers.is_empty() {
            return Err("an ordinary `example` unexpectedly exported environment effects".into());
        }
        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.proof.len(),
            &verification.fact,
            &verification.well_definedness,
            &verification.domain,
            &verification.proof_steps,
            &verification.conclusion_checks,
        )?
        else {
            return Ok(false);
        };

        body.local_proof_lines
            .push(format!("exact {}", body.conclusion_proof));
        self.declarations.push(format!(
            "example : {} := by\n{}",
            body.proposition,
            indent_lines(&body.local_proof_lines.join("\n"), 2)
        ));
        self.next_fact_name_index += 1;
        Ok(true)
    }
}
