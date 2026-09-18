use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::{
    ExecFactStmtResult, VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

// Dispatcher mirrors wired ByStmt branches.
pub enum ExecByStmtResult {
    ReflexiveProp(ExecByReflexivePropStmtResult),
    SymmetricProp(ExecBySymmetricPropStmtResult),
    Cases(ExecByCasesStmtResult),
    Contra(ExecByContraStmtResult),
    Induc(ExecByInducStmtResult),
    StrongInduc(ExecByStrongInducStmtResult),
}

impl ExecByStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::ReflexiveProp(r) => r.is_failed(),
            Self::SymmetricProp(r) => r.is_failed(),
            Self::Cases(r) => r.is_failed(),
            Self::Contra(r) => r.is_failed(),
            Self::Induc(r) => r.is_failed(),
            Self::StrongInduc(r) => r.is_failed(),
        }
    }
}

// ---------------------------------------------------------------------------
// reflexive_prop / symmetric_prop
// ---------------------------------------------------------------------------

pub enum ExecByReflexivePropStmtResult {
    Success(ExecByReflexivePropStmtSuccess),
    Failed(ExecByReflexivePropStmtFailed),
}

pub struct ExecByReflexivePropStmtSuccess {
    pub prop: AtomicName,
    pub forall_proof: VerifyFactResult,
}

pub enum ExecByReflexivePropStmtFailed {
    Shape(String),
    PropNotDefined(String),
    WrongArity {
        prop: AtomicName,
        expected: usize,
        actual: usize,
    },
    Forall(VerifyFactResult),
}

impl ExecByReflexivePropStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecBySymmetricPropStmtResult {
    Success(ExecBySymmetricPropStmtSuccess),
    Failed(ExecBySymmetricPropStmtFailed),
}

pub struct ExecBySymmetricPropStmtSuccess {
    pub prop: AtomicName,
    pub forall_proof: VerifyFactResult,
}

pub enum ExecBySymmetricPropStmtFailed {
    Shape(String),
    PropNotDefined(String),
    WrongArity {
        prop: AtomicName,
        expected: usize,
        actual: usize,
    },
    Forall(VerifyFactResult),
}

impl ExecBySymmetricPropStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// Shared proof-body pieces (Fact-only v1)
// ---------------------------------------------------------------------------

pub enum ByProofStepResult {
    Fact(ExecFactStmtResult),
}

pub enum ByProofBodyFailed {
    NonFactStmt {
        step_index: usize,
    },
    FactStep {
        step_index: usize,
        result: ExecFactStmtResult,
    },
}

pub struct ByContradictionClosingSuccess {
    pub impossible: VerifyFactResult,
    pub negated_impossible: VerifyFactResult,
}

pub enum ByContradictionClosingFailed {
    Impossible(VerifyFactResult),
    NegateImpossibleUnsupported(String),
    NegatedImpossible(VerifyFactResult),
}

// ---------------------------------------------------------------------------
// by contra
// ---------------------------------------------------------------------------

pub enum ExecByContraStmtResult {
    Success(ExecByContraStmtSuccess),
    Failed(ExecByContraStmtFailed),
}

// Stage order: goal_wd → negation_assumed → proof_steps → closing → local_env → stored.
pub struct ExecByContraStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub negation_assumed: StoreFactAndInferResult,
    pub proof_steps: Vec<ByProofStepResult>,
    pub closing: ByContradictionClosingSuccess,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByContraStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    NegationUnsupported(String),
    NegationAssume(String),
    ProofBody(ByProofBodyFailed),
    Closing(ByContradictionClosingFailed),
    Store(String),
}

impl ExecByContraStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// by cases
// ---------------------------------------------------------------------------

pub enum ExecByCasesStmtResult {
    Success(ExecByCasesStmtSuccess),
    Failed(ExecByCasesStmtFailed),
}

// Stage order: then_facts_wd → coverage → branches → stored.
pub struct ExecByCasesStmtSuccess {
    pub then_facts_wd: Vec<VerifyFactWellDefinedResult>,
    pub coverage: VerifyFactResult,
    pub branches: Vec<ByCasesBranchSuccess>,
    pub stored: Vec<StoreFactAndInferResult>,
}

pub struct ByCasesBranchSuccess {
    pub assumptions_stored: StoreFactAndInferResult,
    pub proof_steps: Vec<ByProofStepResult>,
    pub closing: ByCasesBranchClosingSuccess,
    pub local_env: Box<ExecEnv>,
}

pub enum ByCasesBranchClosingSuccess {
    ThenFacts(Vec<VerifyFactResult>),
    Impossible(ByContradictionClosingSuccess),
}

pub enum ExecByCasesStmtFailed {
    LengthMismatch(String),
    ThenFactWd {
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    Coverage(VerifyFactResult),
    Branch {
        index: usize,
        failed: ByCasesBranchFailed,
    },
    Store {
        index: usize,
        message: String,
    },
}

pub enum ByCasesBranchFailed {
    AssumeCase(String),
    ProofBody(ByProofBodyFailed),
    ClosingThen {
        then_index: usize,
        result: VerifyFactResult,
    },
    ClosingImpossible(ByContradictionClosingFailed),
}

impl ExecByCasesStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// by induc / by strong_induc
// ---------------------------------------------------------------------------

pub enum ExecByInducStmtResult {
    Success(ExecByInducStmtSuccess),
    Failed(ExecByInducStmtFailed),
}

pub struct ExecByInducStmtSuccess {
    pub goals_wd: Vec<VerifyFactWellDefinedResult>,
    pub body: ByInducBodySuccess,
    pub stored: StoreFactAndInferResult,
}

pub enum ByInducBodySuccess {
    Unstructured(ByInducCaseSuccess),
    Structured {
        base: ByInducCaseSuccess,
        step: ByInducCaseSuccess,
    },
}

pub struct ByInducCaseSuccess {
    pub assumptions_stored: Vec<StoreFactAndInferResult>,
    pub proof_steps: Vec<ByProofStepResult>,
    pub goals_verified: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecByInducStmtFailed {
    GoalWd {
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    BodyShape(String),
    Case(ByInducCaseFailed),
    Store(String),
    NotFullyWired(String),
}

pub enum ByInducCaseFailed {
    Assume(String),
    ProofBody(ByProofBodyFailed),
    Goal {
        index: usize,
        result: VerifyFactResult,
    },
}

impl ExecByInducStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecByStrongInducStmtResult {
    Success(ExecByStrongInducStmtSuccess),
    Failed(ExecByStrongInducStmtFailed),
}

pub struct ExecByStrongInducStmtSuccess {
    pub goals_wd: Vec<VerifyFactWellDefinedResult>,
    pub body: ByInducBodySuccess,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByStrongInducStmtFailed {
    GoalWd {
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    BodyShape(String),
    Case(ByInducCaseFailed),
    Store(String),
    NotFullyWired(String),
}

impl ExecByStrongInducStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
