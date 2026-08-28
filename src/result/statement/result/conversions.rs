//! Conversion of specialized statement outcomes into the canonical outcome.

use crate::prelude::*;

impl From<SuccessStmtResult> for StmtResult {
    fn from(success: SuccessStmtResult) -> Self {
        StmtResult::Success(success)
    }
}

impl From<SuccessFactStmtResult> for StmtResult {
    fn from(success: SuccessFactStmtResult) -> Self {
        StmtResult::Success(SuccessStmtResult::Fact(Box::new(success)))
    }
}

impl From<SuccessUnsafeStmtResult> for StmtResult {
    fn from(success: SuccessUnsafeStmtResult) -> Self {
        SuccessStmtResult::UnsafeStmt(success).into()
    }
}

impl From<SuccessDefinitionStmtResult> for StmtResult {
    fn from(success: SuccessDefinitionStmtResult) -> Self {
        SuccessStmtResult::Definition(success).into()
    }
}

impl From<SuccessByStmtResult> for StmtResult {
    fn from(success: SuccessByStmtResult) -> Self {
        SuccessStmtResult::By(success).into()
    }
}

impl From<SuccessWitnessStmtResult> for StmtResult {
    fn from(success: SuccessWitnessStmtResult) -> Self {
        SuccessStmtResult::Witness(success).into()
    }
}

impl From<SuccessProofBlockStmtResult> for StmtResult {
    fn from(success: SuccessProofBlockStmtResult) -> Self {
        SuccessStmtResult::ProofBlock(success).into()
    }
}

impl From<SuccessCommandStmtResult> for StmtResult {
    fn from(success: SuccessCommandStmtResult) -> Self {
        SuccessStmtResult::Command(success).into()
    }
}

impl From<UnknownGenericStmtResult> for StmtResult {
    fn from(unknown: UnknownGenericStmtResult) -> Self {
        StmtResult::Unknown(UnknownStmtResult::Generic(Box::new(unknown)))
    }
}

impl From<UnknownFactResult> for StmtResult {
    fn from(unknown: UnknownFactResult) -> Self {
        StmtResult::Unknown(UnknownStmtResult::Fact(Box::new(unknown)))
    }
}
