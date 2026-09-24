//! Dispatcher for `TrustBoundaryStmt`: trust / trust have.

use super::exec_trust_have_stmt::ExecTrustHaveStmtResult;
use super::exec_trust_stmt::ExecTrustStmtResult;
use crate::new_pipeline::ast::stmt::TrustBoundaryStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum ExecTrustBoundaryStmtResult {
    TrustStmt(ExecTrustStmtResult),
    TrustHaveStmt(ExecTrustHaveStmtResult),
}

impl ExecTrustBoundaryStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::TrustStmt(r) => r.is_failed(),
            Self::TrustHaveStmt(r) => r.is_failed(),
        }
    }
}

impl Runtime {
    pub(in crate::new_pipeline::execute) fn exec_unsafe_stmt(
        &mut self,
        stmt: &TrustBoundaryStmt,
    ) -> RuntimeResult<ExecTrustBoundaryStmtResult> {
        match stmt {
            TrustBoundaryStmt::TrustStmt(trust_stmt) => Ok(ExecTrustBoundaryStmtResult::TrustStmt(
                self.exec_trust_stmt(trust_stmt)?,
            )),
            TrustBoundaryStmt::TrustHaveStmt(trust_have_stmt) => Ok(ExecTrustBoundaryStmtResult::TrustHaveStmt(
                self.exec_trust_have_stmt(trust_have_stmt)?,
            )),
        }
    }
}
