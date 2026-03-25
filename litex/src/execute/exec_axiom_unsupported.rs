use super::Runtime;
use crate::error::RuntimeError;
use crate::result::NonErrStmtExecResult;
use crate::stmt::axiom_stmt::{ByCartDefAxiomStmt, ByFnDefAxiomStmt};
use crate::stmt::Stmt;

impl<'a> Runtime<'a> {
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

