use super::Runtime;
use crate::error::{ExecStmtError, RuntimeError};
use crate::infer::InferResult;
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use crate::stmt::prove_stmt::ProveStmt;
use crate::stmt::Stmt;

impl<'a> Runtime<'a> {
    pub fn exec_prove_stmt(
        &mut self,
        stmt: &ProveStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.runtime_context.push_env();
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for proof_stmt in &stmt.proof {
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    self.runtime_context.pop_env();
                    return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                        Stmt::ProveStmt(stmt.clone()),
                        proof_stmt.to_string(),
                        Some(statement_error),
                        inside_results,
                    )));
                }
            }
        }
        self.runtime_context.pop_env();

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ProveStmt(stmt.clone()),
                InferResult::new(),
                inside_results,
            ),
        ))
    }
}
