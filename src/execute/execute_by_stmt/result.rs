use crate::ast::fact::{AndChainAtomicFact, AtomicFact, Fact};
use crate::ast::names::AtomicName;
use crate::ast::obj::FnSet;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::{
    ExecFactStmtResult, VerifyFactResult, VerifyFactWellDefinedResult, VerifyObjWellDefinedResult,
};
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreFactAndInferResult;

// `local_env` on by-stmt Success (and nested branch/case Success):
// Taken ExecEnv for that statement's local proof / instantiation scope.
// It is the FactId / WdId → entity table for ids cited by Store* / Verify*
// under that scope. Success carries the *route* (stage proofs + id cites);
// resolve payloads through `local_env` (and the parent env for `stored`).
// Do not scrape `local_env` to rediscover a proof. Export ignores env scraping.

// Dispatcher mirrors wired ByStmt branches.
pub enum ExecByStmtResult {
    Cases(ExecByCasesStmtResult),
    Contra(ExecByContraStmtResult),
    Def(ExecByDefStmtResult),
    Extension(ExecByExtensionStmtResult),
    FnExtension(ExecByFnExtensionStmtResult),
    EnumerateFiniteSet(ExecByEnumerateFiniteSetStmtResult),
    For(ExecByForStmtResult),
    Thm(ExecByThmStmtResult),
    Induc(ExecByInducStmtResult),
    StrongInduc(ExecByStrongInducStmtResult),
}

impl ExecByStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Cases(r) => r.is_failed(),
            Self::Contra(r) => r.is_failed(),
            Self::Def(r) => r.is_failed(),
            Self::Extension(r) => r.is_failed(),
            Self::FnExtension(r) => r.is_failed(),
            Self::EnumerateFiniteSet(r) => r.is_failed(),
            Self::For(r) => r.is_failed(),
            Self::Thm(r) => r.is_failed(),
            Self::Induc(r) => r.is_failed(),
            Self::StrongInduc(r) => r.is_failed(),
        }
    }
}

// ---------------------------------------------------------------------------
// extension
// ---------------------------------------------------------------------------

pub enum ExecByExtensionStmtResult {
    Success(ExecByExtensionStmtSuccess),
    Failed(ExecByExtensionStmtFailed),
}

// Stage order: goal_wd → proof_steps → left_to_right → right_to_left → local_env → stored.
pub struct ExecByExtensionStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub proof_steps: Vec<ByProofStepResult>,
    pub left_to_right: VerifyFactResult,
    pub right_to_left: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByExtensionStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    ProofBody(ByProofBodyFailed),
    LeftToRight(VerifyFactResult),
    RightToLeft(VerifyFactResult),
    Store(String),
}

impl ExecByExtensionStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// fn_extension
// ---------------------------------------------------------------------------

pub enum ExecByFnExtensionStmtResult {
    Success(ExecByFnExtensionStmtSuccess),
    Failed(ExecByFnExtensionStmtFailed),
}

// Stage order: goal_wd → carrier → proof_steps → pointwise_proof → local_env → stored.
pub struct ExecByFnExtensionStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub carrier: FnSet,
    pub proof_steps: Vec<ByProofStepResult>,
    pub pointwise_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByFnExtensionStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    NoCompatibleFnSet,
    ProofBody(ByProofBodyFailed),
    Pointwise(VerifyFactResult),
    Store(String),
}

impl ExecByFnExtensionStmtResult {
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
    // No supported definition, or its defining obligations did not verify.
    DefinitionUnavailable,
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


// ---------------------------------------------------------------------------
// enumerate finite_set / for / enumerate range / closed_range as cases
// ---------------------------------------------------------------------------

pub enum ExecByEnumerateFiniteSetStmtResult {
    Success(ExecByEnumerateFiniteSetStmtSuccess),
    Failed(ExecByEnumerateFiniteSetStmtFailed),
}

pub struct ExecByEnumerateFiniteSetStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub assignments: Vec<EnumerateAssignmentSuccess>,
    pub stored: StoreFactAndInferResult,
}

pub struct EnumerateAssignmentSuccess {
    pub then_proofs: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecByEnumerateFiniteSetStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    Domain(String),
    Assignment {
        index: usize,
        then_index: usize,
        result: VerifyFactResult,
    },
    Instantiate(String),
    Store(String),
}

impl ExecByEnumerateFiniteSetStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecByForStmtResult {
    Success(ExecByForStmtSuccess),
    Failed(ExecByForStmtFailed),
}

pub struct ExecByForStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub assignments: Vec<EnumerateAssignmentSuccess>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByForStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    Domain(String),
    Assignment {
        index: usize,
        then_index: usize,
        result: VerifyFactResult,
    },
    Instantiate(String),
    Store(String),
}

impl ExecByForStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecExpandRangeStmtResult {
    Success(ExecExpandRangeStmtSuccess),
    Failed(ExecExpandRangeStmtFailed),
}

pub struct ExecExpandRangeStmtSuccess {
    pub values: Vec<crate::ast::obj::Obj>,
    pub membership: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecExpandRangeStmtFailed {
    Domain(String),
    Membership(VerifyFactResult),
    Store(String),
}

impl ExecExpandRangeStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// release regularity_axiom / axiom_of_choice / zorn_lemma
// ---------------------------------------------------------------------------

pub enum ExecReleaseRegularityAxiomStmtResult {
    Success(ExecReleaseRegularityAxiomStmtSuccess),
    Failed(ExecReleaseRegularityAxiomStmtFailed),
}

// Stage order: set_wd → nonempty → stored (trusted regularity conclusion).
pub struct ExecReleaseRegularityAxiomStmtSuccess {
    pub set_wd: VerifyObjWellDefinedResult,
    pub nonempty: VerifyFactResult,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecReleaseRegularityAxiomStmtFailed {
    SetWd(VerifyObjWellDefinedResult),
    Nonempty(VerifyFactResult),
    Store(String),
}

impl ExecReleaseRegularityAxiomStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecReleaseAxiomOfChoiceStmtResult {
    Success(ExecReleaseAxiomOfChoiceStmtSuccess),
    Failed(ExecReleaseAxiomOfChoiceStmtFailed),
}

// Stage order: family_wd → proof_steps → obligations → local_env → stored.
pub struct ExecReleaseAxiomOfChoiceStmtSuccess {
    pub family_wd: VerifyObjWellDefinedResult,
    pub proof_steps: Vec<ByProofStepResult>,
    pub obligations: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecReleaseAxiomOfChoiceStmtFailed {
    FamilyWd(VerifyObjWellDefinedResult),
    ProofBody(ByProofBodyFailed),
    Obligation {
        index: usize,
        result: VerifyFactResult,
    },
    Store(String),
}

impl ExecReleaseAxiomOfChoiceStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecReleaseZornLemmaStmtResult {
    Success(ExecReleaseZornLemmaStmtSuccess),
    Failed(ExecReleaseZornLemmaStmtFailed),
}

// Stage order: set_wd → prop interface checks → proof_steps → obligations → local_env → stored.
pub struct ExecReleaseZornLemmaStmtSuccess {
    pub set_wd: VerifyObjWellDefinedResult,
    pub proof_steps: Vec<ByProofStepResult>,
    pub obligations: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecReleaseZornLemmaStmtFailed {
    SetWd(VerifyObjWellDefinedResult),
    PropInterface(String),
    ProofBody(ByProofBodyFailed),
    Obligation {
        index: usize,
        result: VerifyFactResult,
    },
    Store(String),
}

impl ExecReleaseZornLemmaStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
