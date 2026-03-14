use crate::error::StmtError;
use crate::stmt::prove_stmt::ProveStmt;
use crate::result::NonErrStmtResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_prove_stmt(&mut self, stmt: &ProveStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }
}
