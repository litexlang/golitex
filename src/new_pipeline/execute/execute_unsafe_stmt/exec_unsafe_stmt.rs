//! Dispatcher for `UnsafeStmt`: trust / trust have.

use super::exec_trust_have_stmt::ExecTrustHaveStmtResult;
use super::exec_trust_stmt::ExecTrustStmtResult;
use crate::new_pipeline::ast::stmt::UnsafeStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

/// Mirrors `UnsafeStmt`.
pub enum ExecUnsafeStmtResult {
    TrustStmt(ExecTrustStmtResult),
    TrustHaveStmt(ExecTrustHaveStmtResult),
}

impl Runtime {
    pub fn exec_unsafe_stmt(&mut self, stmt: &UnsafeStmt) -> RuntimeResult<ExecUnsafeStmtResult> {
        match stmt {
            UnsafeStmt::TrustStmt(trust_stmt) => Ok(ExecUnsafeStmtResult::TrustStmt(
                self.exec_trust_stmt(trust_stmt)?,
            )),
            UnsafeStmt::TrustHaveStmt(trust_have_stmt) => Ok(ExecUnsafeStmtResult::TrustHaveStmt(
                self.exec_trust_have_stmt(trust_have_stmt)?,
            )),
        }
    }
}
