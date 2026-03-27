use super::Runtime;
use crate::error::RuntimeError;
use crate::infer::InferResult;
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use crate::stmt::tooling_stmt::{ClearStmt, DoNothingStmt, ImportStmt, RunFileStmt};
use crate::stmt::Stmt;

impl Runtime {
    pub fn exec_import_stmt(
        &mut self,
        stmt: &ImportStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ImportStmt(stmt.clone()))
    }

    pub fn exec_clear_stmt(
        &mut self,
        stmt: &ClearStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ClearStmt(stmt.clone()))
    }

    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DoNothingStmt(stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ));
    }

    pub fn exec_run_file_stmt(
        &mut self,
        stmt: &RunFileStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::RunFileStmt(stmt.clone()))
    }
}
