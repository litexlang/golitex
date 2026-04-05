use crate::prelude::*;

impl Runtime {
    pub fn exec_by_cart_stmt(
        &mut self,
        stmt: &ByCartStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ByCartStmt(stmt.clone()))
    }
}
