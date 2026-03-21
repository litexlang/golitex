use crate::error::StmtError;
use crate::stmt::axiom_stmt::{
    ByCasesAxiomStmt, ByContraAxiomStmt, EnumerateAxiomStmt, ByInducAxiomStmt,
    ForAxiomStmt, ByExtensionAxiomStmt, ByFnDefAxiomStmt, ByCartDefAxiomStmt,
};
use crate::result::NonErrStmtExecResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_by_cases_axiom_stmt(&mut self, stmt: &ByCasesAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_contra_axiom_stmt(&mut self, stmt: &ByContraAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_enumerate_axiom_stmt(&mut self, stmt: &EnumerateAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_induc_axiom_stmt(&mut self, stmt: &ByInducAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_for_axiom_stmt(&mut self, stmt: &ForAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_extension_axiom_stmt(&mut self, stmt: &ByExtensionAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_fn_def_axiom_stmt(&mut self, stmt: &ByFnDefAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_cart_def_axiom_stmt(&mut self, stmt: &ByCartDefAxiomStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }
}
