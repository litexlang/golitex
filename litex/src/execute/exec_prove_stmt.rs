use crate::error::StmtError;
use crate::infer::InferResult;
use crate::stmt::prove_stmt::ProveStmt;
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_prove_stmt(&mut self, stmt: &ProveStmt) -> Result<NonErrStmtExecResult, StmtError> {
        let mut inside_results = vec![];
        for proof_stmt in &stmt.proof {
            let result = self.exec_stmt(proof_stmt)?;
            inside_results.push(result);
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(
            "prove statement".to_string(),
            InferResult::new(),
            inside_results,
            stmt.line_file,
        )))
    }
}
