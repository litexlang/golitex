use crate::error::StmtError;
use crate::stmt::proof_technique_stmt::{
    ProveCaseByCaseStmt, ProveByContradictionStmt, ProveByEnumerationStmt, ProveByInductionStmt,
    ProveForStmt, ProveByEqualSetStmt, ViewFnAsSetStmt,
};
use crate::result::NonErrStmtResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_prove_case_by_case_stmt(&mut self, stmt: &ProveCaseByCaseStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_prove_by_contradiction_stmt(&mut self, stmt: &ProveByContradictionStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_prove_by_enumeration_stmt(&mut self, stmt: &ProveByEnumerationStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_prove_by_induction_stmt(&mut self, stmt: &ProveByInductionStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_prove_for_stmt(&mut self, stmt: &ProveForStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_prove_by_equal_set_stmt(&mut self, stmt: &ProveByEqualSetStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_view_fn_as_set_stmt(&mut self, stmt: &ViewFnAsSetStmt) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }
}
