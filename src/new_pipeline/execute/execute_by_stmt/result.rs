use crate::new_pipeline::ast::fact::{AndChainAtomicFact, AtomicFact, Fact};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::{
    ExecFactStmtResult, VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::new_pipeline::runtime::FactId;
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

// `local_env` on by-stmt Success (and nested branch/case Success):
// Taken ExecEnv for that statement's local proof / instantiation scope.
// It is the FactId / WdId → entity table for ids cited by Store* / Verify*
// under that scope. Success carries the *route* (stage proofs + id cites);
// resolve payloads through `local_env` (and the parent env for `stored`).
// Do not scrape `local_env` to rediscover a proof. Export ignores env scraping.

// Dispatcher mirrors wired ByStmt branches.
pub enum ExecByStmtResult {
    ReflexiveProp(ExecByReflexivePropStmtResult),
    SymmetricProp(ExecBySymmetricPropStmtResult),
    Cases(ExecByCasesStmtResult),
    Contra(ExecByContraStmtResult),
    Def(ExecByDefStmtResult),
    Thm(ExecByThmStmtResult),
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
            Self::Def(r) => r.is_failed(),
            Self::Thm(r) => r.is_failed(),
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
    pub impossible_fact: AtomicFact,
    pub impossible: VerifyFactResult,
    pub negated_impossible: VerifyFactResult,
    // Present when that atom was already known in the local env (cite handle).
    pub impossible_fact_id: Option<FactId>,
    pub negated_impossible_fact_id: Option<FactId>,
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
// Lean-replay cites: goal / reverse_assumption(+fact_id) / assumption_components / closing.
pub struct ExecByContraStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub goal: Fact,
    pub reverse_assumption: Fact,
    pub reverse_assumption_fact_id: FactId,
    pub assumption_components: Vec<(FactId, AtomicFact)>,
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

// Lean-replay cites: assumption(+fact_id) / assumption_components / closing.
pub struct ByCasesBranchSuccess {
    pub assumption: AndChainAtomicFact,
    pub assumption_fact_id: FactId,
    pub assumption_components: Vec<(FactId, AtomicFact)>,
    pub assumptions_stored: StoreFactAndInferResult,
    pub proof_steps: Vec<ByProofStepResult>,
    pub closing: ByCasesBranchClosingSuccess,
    pub local_env: Box<ExecEnv>,
}

pub enum ByCasesBranchClosingSuccess {
    ThenFacts {
        checks: Vec<VerifyFactResult>,
        // Aligned with `then_facts`; Some when the branch stored that conclusion locally.
        conclusion_fact_ids: Vec<Option<FactId>>,
    },
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
// by def
// ---------------------------------------------------------------------------

pub enum ExecByDefStmtResult {
    Success(ExecByDefStmtSuccess),
    Failed(ExecByDefStmtFailed),
}

// Stage order: goal_wd → proof → local_env → stored.
pub struct ExecByDefStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByDefStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    Proof(VerifyFactResult),
    Store(String),
}

impl ExecByDefStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// release thm (top-level Stmt; result lives here next to by thm)
// ---------------------------------------------------------------------------

pub enum ExecReleaseThmStmtResult {
    Success(ExecReleaseThmStmtSuccess),
    Failed(ExecReleaseThmStmtFailed),
}

// Stage order: dom_proofs → local_env → stored conclusions.
pub struct ExecReleaseThmStmtSuccess {
    pub thm_name: String,
    pub dom_proofs: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: Vec<StoreFactAndInferResult>,
}

pub enum ExecReleaseThmStmtFailed {
    ThmNotFound(String),
    Shape(String),
    Dom {
        index: usize,
        result: VerifyFactResult,
    },
    Instantiate(String),
    Store {
        index: usize,
        message: String,
    },
}

impl ExecReleaseThmStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// by thm
// ---------------------------------------------------------------------------

pub enum ExecByThmStmtResult {
    Success(ExecByThmStmtSuccess),
    Failed(ExecByThmStmtFailed),
}

// Stage order: release (into local) → selected_proof → local_env → stored.
pub struct ExecByThmStmtSuccess {
    pub thm_name: String,
    pub dom_proofs: Vec<VerifyFactResult>,
    pub selected_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByThmStmtFailed {
    Release(ExecReleaseThmStmtFailed),
    Selected(VerifyFactResult),
    Store(String),
}

impl ExecByThmStmtResult {
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
