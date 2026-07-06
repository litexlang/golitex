use crate::prelude::*;

#[derive(Debug)]
pub enum UnsafeStmtResult {
    ProofDebtStmt(NonFactualStmtSuccess),
    DefLetStmt(NonFactualStmtSuccess),
}

impl UnsafeStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::UnsafeStmt(UnsafeStmt::ProofDebtStmt(_)) => {
                UnsafeStmtResult::ProofDebtStmt(success)
            }
            Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(_)) => UnsafeStmtResult::DefLetStmt(success),
            _ => panic!("expected unsafe stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            UnsafeStmtResult::ProofDebtStmt(success) | UnsafeStmtResult::DefLetStmt(success) => {
                success
            }
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            UnsafeStmtResult::ProofDebtStmt(success) | UnsafeStmtResult::DefLetStmt(success) => {
                success
            }
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            UnsafeStmtResult::ProofDebtStmt(success) | UnsafeStmtResult::DefLetStmt(success) => {
                success
            }
        }
    }
}
