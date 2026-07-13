use crate::prelude::*;

#[derive(Debug)]
pub enum UnsafeStmtResult {
    TrustStmt(NonFactualStmtSuccess),
    TrustHaveStmt(NonFactualStmtSuccess),
}

impl UnsafeStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(_)) => UnsafeStmtResult::TrustStmt(success),
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(_)) => {
                UnsafeStmtResult::TrustHaveStmt(success)
            }
            _ => panic!("expected unsafe stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            UnsafeStmtResult::TrustStmt(success) | UnsafeStmtResult::TrustHaveStmt(success) => {
                success
            }
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            UnsafeStmtResult::TrustStmt(success) | UnsafeStmtResult::TrustHaveStmt(success) => {
                success
            }
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            UnsafeStmtResult::TrustStmt(success) | UnsafeStmtResult::TrustHaveStmt(success) => {
                success
            }
        }
    }
}
