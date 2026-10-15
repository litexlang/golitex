use crate::ast::stmt::ClaimStmt;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_fact_stmt::{
    AssumeDomFactResult, VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::execute::IntroduceTypedParametersResult;
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
    pub statement: crate::ast::stmt::Stmt,
    pub result: Box<ExecStmtResult>,
}

// ---------------------------------------------------------------------------
// claim
// ---------------------------------------------------------------------------

pub enum ExecClaimStmtResult {
    Success(ExecClaimStmtSuccess),
    Failed(ExecClaimStmtFailed),
}

// Original source, then stage order: goal_wd → body → local_env → stored.
pub struct ExecClaimStmtSuccess {
    pub statement: ClaimStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub body: ExecClaimBodyProof,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecClaimBodyProof {
    NonForall(ExecClaimNonForallProof),
    Forall(ExecClaimForallProof),
}

pub struct ExecClaimNonForallProof {
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proof: VerifyFactResult,
}

pub struct ExecClaimForallProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proofs: Vec<VerifyFactResult>,
}

impl ExecClaimBodyProof {
    pub fn proof_steps(&self) -> &[ExecStmtResult] {
        match self {
            Self::NonForall(body) => &body.proof_steps,
            Self::Forall(body) => &body.proof_steps,
        }
    }

    pub fn conclusion_proofs(&self) -> &[VerifyFactResult] {
        match self {
            Self::NonForall(body) => std::slice::from_ref(&body.conclusion_proof),
            Self::Forall(body) => &body.conclusion_proofs,
        }
    }
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
