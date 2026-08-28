//! Try statement compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_try_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTryStmtResult,
    ) -> Result<(), String> {
        let proof = result
            .proof
            .as_ref()
            .ok_or_else(|| "successful `try` retained no child results".to_string())?;
        if proof.proof_steps.len() != result.statement.proof.len() {
            return Err("successful `try` changed its source statement order".into());
        }
        for child in &proof.proof_steps {
            self.compile_stmt_result(child)?;
        }
        Ok(())
    }
}
