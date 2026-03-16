use crate::error::StmtError;
use crate::stmt::prove_stmt::ProveStmt;
use crate::result::NonErrStmtExecResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_prove_stmt(&mut self, stmt: &ProveStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }
}
