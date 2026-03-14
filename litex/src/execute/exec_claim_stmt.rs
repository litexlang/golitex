use crate::error::StmtError;
use crate::stmt::claim_stmt::ClaimStmt;
use crate::result::NonErrStmtResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file())
    }
}
