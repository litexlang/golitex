use crate::error::StmtError;
use crate::stmt::tooling_stmt::{ImportStmt, ClearStmt, DoNothingStmt, RunFileStmt};
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use super::Executor;
use crate::infer::InferResult;

impl<'a> Executor<'a> {
    pub fn exec_import_stmt(&mut self, stmt: &ImportStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file())
    }

    pub fn exec_clear_stmt(&mut self, stmt: &ClearStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }

    pub fn exec_do_nothing_stmt(&mut self, stmt: &DoNothingStmt) -> Result<NonErrStmtExecResult, StmtError> {
        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(stmt.to_string(), InferResult::new(), stmt.line_file_index)));
    }

    pub fn exec_run_file_stmt(&mut self, stmt: &RunFileStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }
}
