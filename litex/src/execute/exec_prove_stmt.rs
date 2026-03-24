use super::Runtime;
use crate::error::{ExecStmtError, StmtError};
use crate::infer::InferResult;
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use crate::stmt::prove_stmt::ProveStmt;

impl<'a> Runtime<'a> {
    pub fn exec_prove_stmt(&mut self, stmt: &ProveStmt) -> Result<NonErrStmtExecResult, StmtError> {
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for proof_stmt in &stmt.proof {
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(StmtError::ExecError(
                        ExecStmtError::new(
                            stmt.stmt_type_name(),
                            proof_stmt.to_string(),
                            Some(statement_error),
                            inside_results,
                            stmt.line_file,
                        ),
                    ));
                }
            }
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                "prove statement".to_string(),
                InferResult::new(),
                inside_results,
                stmt.line_file,
            ),
        ))
    }
}
