//! Dispatcher for `UnsafeStmt`: trust / trust have.

use super::exec_trust_have_stmt::ExecTrustHaveStmtResult;
use super::exec_trust_stmt::ExecTrustStmtResult;
use crate::new_pipeline::ast::stmt::UnsafeStmt;
use crate::new_pipeline::execute::exec_stmt_result::ExecUnsafeStmtFailed;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum ExecUnsafeStmtResult {
    TrustStmt(ExecTrustStmtResult),
    TrustHaveStmt(ExecTrustHaveStmtResult),
}

impl Runtime {
    pub(in crate::new_pipeline::execute) fn exec_unsafe_stmt(
        &mut self,
        stmt: &UnsafeStmt,
    ) -> RuntimeResult<Result<ExecUnsafeStmtResult, ExecUnsafeStmtFailed>> {
        match stmt {
            UnsafeStmt::TrustStmt(trust_stmt) => match self.exec_trust_stmt(trust_stmt)? {
                Ok(r) => Ok(Ok(ExecUnsafeStmtResult::TrustStmt(r))),
                Err(verify_result) => Ok(Err(ExecUnsafeStmtFailed::Trust(verify_result))),
            },
            UnsafeStmt::TrustHaveStmt(trust_have_stmt) => {
                match self.exec_trust_have_stmt(trust_have_stmt)? {
                    Ok(r) => Ok(Ok(ExecUnsafeStmtResult::TrustHaveStmt(r))),
                    Err(failed) => Ok(Err(ExecUnsafeStmtFailed::TrustHave(failed))),
                }
            }
        }
    }
}
