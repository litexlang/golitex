use super::Executor;
use crate::error::StmtError;
use crate::result::NonErrStmtExecResult;
use crate::stmt::eval_stmt::EvalStmt;

impl<'a> Executor<'a> {
    pub fn exec_eval_stmt(&mut self, stmt: &EvalStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }
}
