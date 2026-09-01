//! Successful claim, example, sketch, and try-block outcomes.

use crate::prelude::*;

pub struct SuccessClaimStmtResult {
    pub statement: ClaimStmt,
    pub well_definedness: Option<SuccessVerifyFactWellDefinedResult>,
    pub domain: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
    pub environment_effects: SuccessInferResult,
}

impl SuccessClaimStmtResult {
    pub fn checked(
        statement: ClaimStmt,
        verification: SuccessCheckedGoalBlockResult,
        environment_effects: SuccessInferResult,
    ) -> Self {
        debug_assert_eq!(statement.fact.to_string(), verification.fact.to_string());
        Self {
            statement,
            well_definedness: Some(verification.well_definedness),
            domain: verification.domain,
            proof_steps: verification.proof_steps,
            conclusion_checks: verification.conclusion_checks,
            environment_effects,
        }
    }

    pub fn with_trust(statement: ClaimStmt, environment_effects: SuccessInferResult) -> Self {
        Self {
            statement,
            well_definedness: None,
            domain: SuccessVerifyLocalProofScopeResult::new(SuccessInferResult::new(), Vec::new()),
            proof_steps: Vec::new(),
            conclusion_checks: Vec::new(),
            environment_effects,
        }
    }
}

pub struct SuccessExampleStmtResult {
    pub statement: ExampleStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessCheckedGoalBlockResult>,
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
    /// Whether the successful `try` statement committed or rolled back its
    /// isolated body. A rollback is diagnostic data, not a statement failure.
    pub execution: TryStmtExecutionResult,
}

pub enum TryStmtExecutionResult {
    Committed(SuccessTryProofResult),
    RolledBack(RuntimeError),
    SkippedByTrustedExecution,
}

pub enum SuccessProofBlockStmtResult {
    ClaimStmt(Box<SuccessClaimStmtResult>),
    ExampleStmt(Box<SuccessExampleStmtResult>),
    SketchStmt(Box<SuccessSketchStmtResult>),
    TryStmt(Box<SuccessTryStmtResult>),
}
