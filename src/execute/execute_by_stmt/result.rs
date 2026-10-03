use crate::ast::fact::{AndChainAtomicFact, AtomicFact, Fact};
use crate::ast::names::AtomicName;
use crate::ast::obj::FnSet;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::{
    ProveAndStoreThenFactResult, VerifyFactResult, VerifyFactWellDefinedResult, VerifyObjWellDefinedResult,
};
use crate::runtime::FactId;
use crate::execute::ExecStmtResult;
use crate::execute::execute_proof_block_stmt::ProofBlockBodyFailed;
use crate::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::execute::execute_fact_stmt::AssumeDomFactResult;
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
    pub proof_steps: Vec<ExecStmtResult>,
    pub left_to_right: VerifyFactResult,
    pub right_to_left: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByExtensionStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    ProofBody(ProofBlockBodyFailed),
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
    pub proof_steps: Vec<ExecStmtResult>,
    pub pointwise_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByFnExtensionStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    NoCompatibleFnSet,
    ProofBody(ProofBlockBodyFailed),
    Pointwise(VerifyFactResult),
    Store(String),
}

impl ExecByFnExtensionStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub struct ByContradictionClosingSuccess {
    pub impossible_fact: Fact,
    pub impossible: VerifyFactResult,
    pub negated_impossible: VerifyFactResult,
    // Present only when the exact fact was already known in the local env.
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
    pub proof_steps: Vec<ExecStmtResult>,
    pub closing: ByContradictionClosingSuccess,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByContraStmtFailed {
    GoalWd(VerifyFactWellDefinedResult),
    NegationUnsupported(String),
    NegationAssume(String),
    ProofBody(ProofBlockBodyFailed),
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
    pub proof_steps: Vec<ExecStmtResult>,
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
    ProofBody(ProofBlockBodyFailed),
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

// Reserved builtin application metadata is separate from verified premises.
// The proof results below certify each requirement in this contract in order.
pub struct BuiltinThmApplication {
    pub theorem: crate::builtin_theorem::BuiltinTheoremId,
    pub arguments: Vec<crate::ast::obj::Obj>,
    pub requirements: Vec<Fact>,
    pub conclusions: Vec<Fact>,
}

pub enum ExecReleaseThmStmtResult {
    Success(ExecReleaseThmStmtSuccess),
    Failed(ExecReleaseThmStmtFailed),
}

// Stage order: type_proofs → dom_proofs → local_env → stored conclusions.
pub struct ExecReleaseThmStmtSuccess {
    pub thm_name: String,
    pub builtin: Option<BuiltinThmApplication>,
    pub type_proofs: Vec<VerifyFactResult>,
    pub dom_proofs: Vec<VerifyFactResult>,
    pub conclusions_wd: Vec<crate::execute::execute_fact_stmt::FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
    pub stored: Vec<StoreFactAndInferResult>,
}

pub enum ExecReleaseThmStmtFailed {
    BuiltinArity { theorem: crate::builtin_theorem::BuiltinTheoremId, expected: usize, actual: usize },
    BuiltinShape { theorem: crate::builtin_theorem::BuiltinTheoremId, message: String },
    ThmNotFound(String),
    Shape(String),
    Type {
        theorem: String,
        fact: Fact,
        index: usize,
        result: VerifyFactResult,
    },
    Dom {
        theorem: String,
        fact: Fact,
        index: usize,
        result: VerifyFactResult,
    },
    Instantiate(String),
    ConclusionWd {
        theorem: String,
        fact: Fact,
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    Store {
        theorem: String,
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

// Stage order: type_proofs → dom_proofs → selected_proof → local_env → stored.
pub struct ExecByThmStmtSuccess {
    pub thm_name: String,
    pub builtin: Option<BuiltinThmApplication>,
    pub type_proofs: Vec<VerifyFactResult>,
    pub dom_proofs: Vec<VerifyFactResult>,
    pub conclusions_wd: Vec<crate::execute::execute_fact_stmt::FactWellDefinedProof>,
    pub selected_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByThmStmtFailed {
    Release(ExecReleaseThmStmtFailed),
    Selected { theorem: String, fact: Fact, result: VerifyFactResult },
    Store { theorem: String, message: String },
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
    pub from_in_z: VerifyFactResult,
    pub goal_domain_stored: StoreFactAndInferResult,
    pub goals_wd: Vec<VerifyFactWellDefinedResult>,
    pub goal_wd_env: Box<ExecEnv>,
    pub body: ByInducBodySuccess,
    pub stored: StoreFactAndInferResult,
}

pub enum ByInducBodySuccess {
    Unstructured {
        base: ByInducCaseSuccess,
        step: ByInducCaseSuccess,
    },
    Structured {
        base: ByInducCaseSuccess,
        step: ByInducCaseSuccess,
    },
}

pub struct ByInducCaseSuccess {
    pub assumptions_stored: Vec<StoreFactAndInferResult>,
    pub proof_steps: Vec<crate::execute::ExecStmtResult>,
    pub goals_verified: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecByInducStmtFailed {
    FromNotInteger(VerifyFactResult),
    GoalDomain(String),
    GoalWd {
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    BodyShape(String),
    BaseCase(ByInducCaseFailed),
    StepCase(ByInducCaseFailed),
    Store(String),
    NotFullyWired(String),
}

pub enum ByInducCaseFailed {
    Assume(String),
    ProofBody(crate::execute::execute_proof_block_stmt::ProofBlockBodyFailed),
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
    pub from_in_z: VerifyFactResult,
    pub goal_domain_stored: StoreFactAndInferResult,
    pub goals_wd: Vec<VerifyFactWellDefinedResult>,
    pub goal_wd_env: Box<ExecEnv>,
    pub body: ByInducBodySuccess,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecByStrongInducStmtFailed {
    FromNotInteger(VerifyFactResult),
    GoalDomain(String),
    GoalWd {
        index: usize,
        result: VerifyFactWellDefinedResult,
    },
    BodyShape(String),
    BaseCase(ByInducCaseFailed),
    StepCase(ByInducCaseFailed),
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
    pub introduced_params: IntroduceTypedParametersResult,
    pub binding_assumptions: Vec<AssumeDomFactResult>,
    pub outcome: EnumerateAssignmentOutcome,
    pub local_env: Box<ExecEnv>,
}

pub enum EnumerateAssignmentOutcome {
    Skipped {
        premise_assumptions: Vec<AssumeDomFactResult>,
        premise_index: usize,
        negated_premise: VerifyFactResult,
    },
    Proved {
        premise_assumptions: Vec<AssumeDomFactResult>,
        proof_steps: Vec<ExecStmtResult>,
        then_proofs: Vec<ProveAndStoreThenFactResult>,
    },
}

pub enum ExecByEnumerateFiniteSetStmtFailed {
    ProofBody(ProofBlockBodyFailed),
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
    ProofBody(ProofBlockBodyFailed),
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
    pub proof_steps: Vec<ExecStmtResult>,
    pub obligations: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecReleaseAxiomOfChoiceStmtFailed {
    FamilyWd(VerifyObjWellDefinedResult),
    ProofBody(ProofBlockBodyFailed),
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
    pub proof_steps: Vec<ExecStmtResult>,
    pub obligations: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecReleaseZornLemmaStmtFailed {
    SetWd(VerifyObjWellDefinedResult),
    PropInterface(String),
    ProofBody(ProofBlockBodyFailed),
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
