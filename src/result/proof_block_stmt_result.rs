use crate::prelude::*;

#[derive(Debug)]
pub enum ProofBlockStmtResult {
    ClaimStmt(NonFactualStmtSuccess),
    SketchStmt(NonFactualStmtSuccess),
}

impl ProofBlockStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(_)) => {
                ProofBlockStmtResult::ClaimStmt(success)
            }
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(_)) => {
                ProofBlockStmtResult::SketchStmt(success)
            }
            _ => panic!("expected proof block stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            ProofBlockStmtResult::ClaimStmt(success)
            | ProofBlockStmtResult::SketchStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            ProofBlockStmtResult::ClaimStmt(success)
            | ProofBlockStmtResult::SketchStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            ProofBlockStmtResult::ClaimStmt(success)
            | ProofBlockStmtResult::SketchStmt(success) => success,
        }
    }
}
