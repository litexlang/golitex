//! Successful claim, example, sketch, and try-block outcomes.

use crate::prelude::*;

pub struct SuccessClaimStmtResult {
    pub statement: ClaimStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyClaimResult>,
}

pub struct SuccessExampleStmtResult {
    pub statement: ExampleStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyClaimResult>,
}

pub struct SuccessSketchProofResult {
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
}

pub struct SuccessSketchStmtResult {
    pub statement: SketchStmt,
    pub common: SuccessStmtCommonResult,
    pub proof: Option<SuccessSketchProofResult>,
}

pub struct SuccessTryProofResult {
    pub proof_steps: Vec<StmtResult>,
}

pub struct SuccessTryStmtResult {
    pub statement: TryStmt,
    pub common: SuccessStmtCommonResult,
    pub proof: Option<SuccessTryProofResult>,
}

pub enum SuccessProofBlockStmtResult {
    ClaimStmt(Box<SuccessClaimStmtResult>),
    ExampleStmt(Box<SuccessExampleStmtResult>),
    SketchStmt(Box<SuccessSketchStmtResult>),
    TryStmt(Box<SuccessTryStmtResult>),
}
