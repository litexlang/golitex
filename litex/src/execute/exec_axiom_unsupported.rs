use crate::prelude::*;

impl Runtime {
    pub fn exec_by_fn_def_axiom_stmt(
        &mut self,
        stmt: &ByFnDefAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ByFnDefAxiomStmt(stmt.clone()))
    }

    pub fn exec_by_cart_def_axiom_stmt(
        &mut self,
        stmt: &ByCartDefAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ByCartDefAxiomStmt(stmt.clone()))
    }
}
