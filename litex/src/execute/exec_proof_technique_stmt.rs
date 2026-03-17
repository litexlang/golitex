use crate::error::StmtError;
use crate::stmt::proof_technique_stmt::{
    ProveCaseByCaseStmt, ProveByContradictionStmt, ProveByEnumerationStmt, ProveByInductionStmt,
    ProveForStmt, ProveByEqualSetStmt, ViewFnAsSetStmt,
};
use crate::result::NonErrStmtExecResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_prove_case_by_case_stmt(&mut self, stmt: &ProveCaseByCaseStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }

    pub fn exec_prove_by_contradiction_stmt(&mut self, stmt: &ProveByContradictionStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }

    pub fn exec_prove_by_enumeration_stmt(&mut self, stmt: &ProveByEnumerationStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }

    pub fn exec_prove_by_induction_stmt(&mut self, stmt: &ProveByInductionStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }

    pub fn exec_prove_for_stmt(&mut self, stmt: &ProveForStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }

    pub fn exec_prove_by_equal_set_stmt(&mut self, stmt: &ProveByEqualSetStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }

    pub fn exec_view_fn_as_set_stmt(&mut self, stmt: &ViewFnAsSetStmt) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file_index)
    }
}
