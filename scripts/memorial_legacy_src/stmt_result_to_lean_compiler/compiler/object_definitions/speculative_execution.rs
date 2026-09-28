//! Try statement compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_try_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTryStmtResult,
    ) -> Result<(), String> {
        match &result.execution {
            TryStmtExecutionResult::Committed(proof) => {
                if proof.proof_steps.len() != result.statement.proof.len() {
                    return Err("committed `try` changed its source statement order".into());
                }
                for child in &proof.proof_steps {
                    self.compile_stmt_result(child)?;
                }
            }
            TryStmtExecutionResult::RolledBack(_)
            | TryStmtExecutionResult::SkippedByTrustedExecution => {
                if !result.common.infers.is_empty() {
                    return Err("non-committed `try` unexpectedly published effects".into());
                }
            }
        }
        Ok(())
    }
}
