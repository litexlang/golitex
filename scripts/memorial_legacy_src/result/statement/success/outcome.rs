//! Top-level successful statement outcome.

use crate::prelude::*;

pub enum SuccessStmtResult {
    Fact(Box<SuccessFactStmtResult>),
    UnsafeStmt(SuccessUnsafeStmtResult),
    Definition(SuccessDefinitionStmtResult),
    ReleaseThmStmt(Box<SuccessReleaseThmStmtResult>),
    ReleaseStructDefStmt(Box<SuccessReleaseStructDefStmtResult>),
    By(SuccessByStmtResult),
    Witness(SuccessWitnessStmtResult),
    ProofBlock(SuccessProofBlockStmtResult),
    Command(SuccessCommandStmtResult),
}
