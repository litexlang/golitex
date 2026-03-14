use crate::error::StmtError;
use crate::stmt::tooling_stmt::{ImportStmt, ClearStmt, DoNothingStmt, RunFileStmt};
use crate::result::NonErrStmtResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_import_stmt(&mut self, stmt: &ImportStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file())
    }

    pub fn exec_clear_stmt(&mut self, stmt: &ClearStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_do_nothing_stmt(&mut self, stmt: &DoNothingStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_run_file_stmt(&mut self, stmt: &RunFileStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }
}
