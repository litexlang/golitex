use crate::error::StmtError;
use crate::stmt::eval_stmt::EvalStmt;
use crate::result::NonErrStmtExecResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_eval_stmt(&mut self, stmt: &EvalStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }
}
