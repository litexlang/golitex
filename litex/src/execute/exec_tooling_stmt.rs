use super::Runtime;
use crate::error::RuntimeError;
use crate::infer::InferResult;
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use crate::stmt::tooling_stmt::{ClearStmt, DoNothingStmt, ImportStmt, RunFileStmt};

impl<'a> Runtime<'a> {
    pub fn exec_import_stmt(
        &mut self,
        stmt: &ImportStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file())
    }

    pub fn exec_clear_stmt(&mut self, stmt: &ClearStmt) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                stmt.to_string(),
                InferResult::new(),
                vec![],
                stmt.line_file,
            ),
        ));
    }

    pub fn exec_run_file_stmt(
        &mut self,
        stmt: &RunFileStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }
}
