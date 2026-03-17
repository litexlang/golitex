use crate::error::StmtError;
use crate::stmt::claim_stmt::ClaimStmt;
use crate::result::NonErrStmtExecResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file())
    }
}
