use super::Runtime;
use crate::error::{ExecStmtError, RuntimeError};
use crate::infer::InferResult;
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use crate::stmt::prove_stmt::ProveStmt;
use crate::stmt::Stmt;

impl Runtime {
    pub fn exec_prove_stmt(
        &mut self,
        stmt: &ProveStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.runtime_context.push_env();
        let inside_results = self.exec_prove_stmt_body(stmt);
        self.runtime_context.pop_env();

        match inside_results {
            Ok(inside_results) => Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::ProveStmt(stmt.clone()),
                    InferResult::new(),
                    inside_results,
                ),
            )),
            Err(inside_results_error) => Err(RuntimeError::from(inside_results_error)),
        }
    }

    fn exec_prove_stmt_body(
        &mut self,
        stmt: &ProveStmt,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for proof_stmt in &stmt.proof {
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            Stmt::ProveStmt(stmt.clone()),
                            proof_stmt.to_string(),
                            Some(statement_error),
                            inside_results,
                        ),
                    ));
                }
            }
        }
        Ok(inside_results)
    }
}
