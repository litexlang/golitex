use super::Runtime;
use crate::error::RuntimeError;
use crate::result::NonErrStmtExecResult;
use crate::stmt::eval_stmt::EvalStmt;

impl<'a> Runtime<'a> {
    pub fn exec_eval_stmt(&mut self, stmt: &EvalStmt) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }
}
