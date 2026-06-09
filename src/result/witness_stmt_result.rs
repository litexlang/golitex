use crate::prelude::*;

#[derive(Debug)]
pub enum WitnessStmtResult {
    WitnessExistFact(NonFactualStmtSuccess),
    WitnessNonemptySet(NonFactualStmtSuccess),
}

impl WitnessStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::Witness(WitnessStmt::WitnessExistFact(_)) => {
                WitnessStmtResult::WitnessExistFact(success)
            }
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(_)) => {
                WitnessStmtResult::WitnessNonemptySet(success)
            }
            _ => panic!("expected witness stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            WitnessStmtResult::WitnessExistFact(success)
            | WitnessStmtResult::WitnessNonemptySet(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            WitnessStmtResult::WitnessExistFact(success)
            | WitnessStmtResult::WitnessNonemptySet(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            WitnessStmtResult::WitnessExistFact(success)
            | WitnessStmtResult::WitnessNonemptySet(success) => success,
        }
    }
}
