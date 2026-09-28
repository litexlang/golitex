use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::store_fact_and_infer::StoreFactAndInferResult;

// Dispatcher mirrors ProofBlockStmt (claim / sketch).
pub enum ExecProofBlockStmtResult {
    Claim(ExecClaimStmtResult),
    Sketch(ExecSketchStmtResult),
}

impl ExecProofBlockStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Claim(r) => r.is_failed(),
            Self::Sketch(r) => r.is_failed(),
        }
    }
}

// Soft-fail inside a proof-block body step.
pub struct ProofBlockBodyFailed {
    pub step_index: usize,
    pub result: Box<ExecStmtResult>,
}

// ---------------------------------------------------------------------------
// claim
// ---------------------------------------------------------------------------

pub enum ExecClaimStmtResult {
    Success(ExecClaimStmtSuccess),
    Failed(ExecClaimStmtFailed),
}

// Stage order: goal_wd → proof_steps → conclusion_proofs → local_env → stored.
pub struct ExecClaimStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proofs: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecClaimStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    GoalUnsupported(String),
    Introduce(String),
    ProofBody(ProofBlockBodyFailed),
    Conclusion {
        index: usize,
        result: VerifyFactResult,
    },
    Store(String),
}

impl ExecClaimStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// sketch
// ---------------------------------------------------------------------------

pub enum ExecSketchStmtResult {
    Success(ExecSketchStmtSuccess),
    Failed(ExecSketchStmtFailed),
}

// Stage order: proof_steps → local_env. Nothing is stored outside.
pub struct ExecSketchStmtSuccess {
    pub proof_steps: Vec<ExecStmtResult>,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecSketchStmtFailed {
    ProofBody(ProofBlockBodyFailed),
}

impl ExecSketchStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
