use crate::ast::fact::{EqualFact, Fact};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualitySearchProofByBuiltinRewrite, EqualitySearchProofByBuiltinRule,
    EqualitySearchProofByBuiltinStrategy, EqualitySearchProofByObjectDefinition,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_matching_one_arg_by_one::EqualFactSearchedProofByMatchingOneArgByOne;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::{
    EqualFactWellDefinedProof, FailToVerifyEqualFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::runtime::runtime_ids::{FactId, IdentifierId};
use super::by_they_are_the_same::TheyAreTheSameProof;
use super::search_equal_fact_proof_by_known_special_property::EqualFactSearchProofByKnownSpecialProperty;

// Shared known-forall application certificate.
// Field order mirrors successful apply stages:
// match args → prove param-type + dom requirements.
// `arg_match_proofs` is one entry per conclusion/goal arg (Lean-aligned).
// Boxed under EqualFactSearchedProof::ByKnownForallFact to break the type cycle.
pub struct SearchProofByKnownForallFact {
    pub cite: crate::exec_env::ForallConclusionCite,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
    pub instantiation_requirements: ProveForallInstantiationRequirementsProof,
}

// After match: prove each instantiated arg meets param type, then prove dom facts.
// Field order = stage order.
pub struct ProveForallInstantiationRequirementsProof {
    pub param_type_requirements: Vec<ForallParamTypeRequirementProof>,
    pub dom_facts: Vec<Fact>,
    pub proof_of_dom_facts: Vec<VerifyFactResult>,
}

// One entry per forall parameter (declaration order).
pub struct ForallParamTypeRequirementProof {
    pub param_id: IdentifierId,
    pub arg: Obj,
    pub type_fact: Fact,
    pub proof: VerifyFactResult,
}

// Output of matching conclusion args to goal args (before dom requirements).
pub struct MatchForallConclusionArgsProof {
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
}

// One slot per (pattern_arg, goal_arg). Length equals arg arity.
// Nested structure peels use ByStructure with the same enum recursively.
pub enum ForallConclusionArgMatchProof {
    // First sight of a forall param: bind goal_arg, no equal subproof.
    BoundParam {
        param_id: IdentifierId,
        pattern: Obj,
        goal_arg: Obj,
    },
    // Same param again: prove previous = goal_arg under strict equal.
    ReboundParamEqual {
        param_id: IdentifierId,
        previous: Obj,
        goal_arg: Obj,
        equal: StrictEqualWithFact,
    },
    // Same constructor shape: recurse on corresponding children (legacy-aligned).
    // Example: pattern `f(a)`, goal `f(t)` → child BoundParam `a↦t`.
    ByStructure {
        pattern: Obj,
        goal_arg: Obj,
        child_matches: Vec<ForallConclusionArgMatchProof>,
    },
    // No same-shape peel: instantiate under current subst, then strict equal
    // (forall/rewrite/store WD off).
    NonParamEqual {
        pattern: Obj,
        pattern_after_subst: Obj,
        goal_arg: Obj,
        equal: StrictEqualWithFact,
    },
}

// EqualFact that was searched, plus a strict (no forall/rewrite) certificate.
pub struct StrictEqualWithFact {
    pub equal_fact: EqualFact,
    pub equal_proof: StrictEqualArgProof,
}

// Equal search routes allowed when matching forall conclusion args.
pub enum StrictEqualArgProof {
    ByTheyAreTheSame(TheyAreTheSameProof),
    ByKnownSpecialProperty(EqualFactSearchProofByKnownSpecialProperty),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByEquivalenceClass(EqualFactSearchedProofByEquivalenceClass),
    ByObjectDefinition(EqualitySearchProofByObjectDefinition),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByMatchingOneArgByOne(EqualFactSearchedProofByMatchingOneArgByOne),
}

pub enum VerifyEqualityResult {
    Success(VerifyEqualitySuccess),
    Failed(VerifyEqualityFailed),
}

pub struct VerifyEqualitySuccess {
    pub fact: EqualFact,
    pub well_defined_proof: EqualFactWellDefinedProof,
    pub searched_proof: EqualFactSearchedProof,
}

pub enum VerifyEqualityFailed {
    FailToVerifyWellDefined(FailToVerifyEqualFactWellDefinedResult),
    FailToSearchProof {
        fact: EqualFact,
        well_defined_proof: EqualFactWellDefinedProof,
    },
}

impl VerifyEqualityResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// Mirrors search_equal_fact_proof stage order.
// MatchingOneArgByOne = constructor peel (not rewrite).
// Rewrite stages replace legacy opaque resolve_obj (ClosedNumeric only).
pub enum EqualFactSearchedProof {
    ByTheyAreTheSame(TheyAreTheSameProof),
    ByKnownSpecialProperty(EqualFactSearchProofByKnownSpecialProperty),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByEquivalenceClass(EqualFactSearchedProofByEquivalenceClass),
    ByObjectDefinition(EqualitySearchProofByObjectDefinition),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByMatchingOneArgByOne(EqualFactSearchedProofByMatchingOneArgByOne),
    ByKnownForallFact(Box<SearchProofByKnownForallFact>),
    // Legacy: match known forall on the swapped equality, then cite symmetry.
    // Example: known `forall x R: f(c, x) = x`, goal `t = f(c, t)`.
    ByKnownForallFactViaSymmetry(Box<EqualFactSearchedProofByKnownForallViaSymmetry>),
    ByBuiltinRewrite(EqualitySearchProofByBuiltinRewrite),
}

// Prove `L = R` by proving `R = L` via known forall, then equality symmetry.
pub struct EqualFactSearchedProofByKnownForallViaSymmetry {
    pub reversed_equal: EqualFact,
    pub known_forall: SearchProofByKnownForallFact,
}

// One search stage, two successful evidence shapes: a stored chain, or two
// stored chains connected by a restricted proof. Never cite a class handle.
pub enum EqualFactSearchedProofByEquivalenceClass {
    KnownPath(KnownEqualityPathProof),
    AlphaEndpoints(KnownEqualityAlphaEndpointsProof),
    ViaPeers(EqualityViaPeersProof),
}

// A cited checked equality, with structural alpha identity at both endpoints.
// The caller's goal WD precedes this search; no class or IR key is rewritten.
pub struct KnownEqualityAlphaEndpointsProof {
    pub cited: EqualFact,
    pub reversed: bool,
    pub left_identity: TheyAreTheSameProof,
    pub right_identity: TheyAreTheSameProof,
}

// Oriented generating edges, each (from, to, cited equality FactId).
// An empty path is identity at the corresponding goal/bridge endpoint.
pub struct KnownEqualityPathProof {
    pub path: Vec<(Obj, Obj, FactId)>,
}

pub struct EqualityViaPeersProof {
    pub left_path: KnownEqualityPathProof,
    pub bridge: PeerEqualitySuccess,
    pub right_path: KnownEqualityPathProof,
}

// Bridge WD precedes its truth proof. The enclosing paths connect the bridge's
// explicit endpoints back to the original goal; failures never enter evidence.
pub struct PeerEqualitySuccess {
    pub fact: EqualFact,
    pub well_defined_proof: EqualFactWellDefinedProof,
    pub searched_proof: PeerEqualitySearchedProof,
}

pub enum PeerEqualitySearchedProof {
    ByTheyAreTheSame(TheyAreTheSameProof),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByMatchingOneArgByOne(EqualFactSearchedProofByMatchingOneArgByOne),
}

impl KnownEqualityPathProof {
    pub fn new(path: Vec<(Obj, Obj, FactId)>) -> Self {
        Self { path }
    }
}

impl EqualityViaPeersProof {
    pub fn new(
        left_path: KnownEqualityPathProof,
        bridge: PeerEqualitySuccess,
        right_path: KnownEqualityPathProof,
    ) -> Self {
        Self { left_path, bridge, right_path }
    }
}

impl PeerEqualitySuccess {
    pub fn new(
        fact: EqualFact,
        well_defined_proof: EqualFactWellDefinedProof,
        searched_proof: PeerEqualitySearchedProof,
    ) -> Self {
        Self { fact, well_defined_proof, searched_proof }
    }
}

impl From<KnownEqualityPathProof> for EqualFactSearchedProofByEquivalenceClass {
    fn from(proof: KnownEqualityPathProof) -> Self { Self::KnownPath(proof) }
}

impl From<EqualityViaPeersProof> for EqualFactSearchedProofByEquivalenceClass {
    fn from(proof: EqualityViaPeersProof) -> Self { Self::ViaPeers(proof) }
}

impl From<TheyAreTheSameProof> for EqualFactSearchedProof {
    fn from(proof: TheyAreTheSameProof) -> Self { Self::ByTheyAreTheSame(proof) }
}

impl From<TheyAreTheSameProof> for PeerEqualitySearchedProof {
    fn from(proof: TheyAreTheSameProof) -> Self { Self::ByTheyAreTheSame(proof) }
}

impl From<EqualitySearchProofByBuiltinRule> for PeerEqualitySearchedProof {
    fn from(proof: EqualitySearchProofByBuiltinRule) -> Self { Self::ByBuiltinRule(proof) }
}

impl From<EqualFactSearchedProofByMatchingOneArgByOne> for PeerEqualitySearchedProof {
    fn from(proof: EqualFactSearchedProofByMatchingOneArgByOne) -> Self { Self::ByMatchingOneArgByOne(proof) }
}

pub fn equal_fact_result_from_wd_fail(
    reason: FailToVerifyEqualFactWellDefinedResult,
) -> VerifyFactResult {
    VerifyFactResult::Equality(Box::new(VerifyEqualityResult::Failed(
        VerifyEqualityFailed::FailToVerifyWellDefined(reason),
    )))
}

pub fn equal_fact_result_from_search_fail(
    fact: &EqualFact,
    well_defined_proof: EqualFactWellDefinedProof,
) -> VerifyFactResult {
    VerifyFactResult::Equality(Box::new(VerifyEqualityResult::Failed(
        VerifyEqualityFailed::FailToSearchProof {
            fact: fact.clone(),
            well_defined_proof,
        },
    )))
}

pub fn equal_fact_result_from_success(
    fact: &EqualFact,
    well_defined_proof: EqualFactWellDefinedProof,
    searched_proof: EqualFactSearchedProof,
) -> VerifyFactResult {
    VerifyFactResult::Equality(Box::new(VerifyEqualityResult::Success(
        VerifyEqualitySuccess {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        },
    )))
}

pub fn strict_equal_arg_proof_from_searched(
    proof: EqualFactSearchedProof,
) -> Option<StrictEqualArgProof> {
    match proof {
        EqualFactSearchedProof::ByTheyAreTheSame(p) => Some(StrictEqualArgProof::ByTheyAreTheSame(p)),
        EqualFactSearchedProof::ByKnownSpecialProperty(p) => Some(StrictEqualArgProof::ByKnownSpecialProperty(p)),
        EqualFactSearchedProof::ByBuiltinRule(p) => Some(StrictEqualArgProof::ByBuiltinRule(p)),
        EqualFactSearchedProof::ByEquivalenceClass(p) => {
            Some(StrictEqualArgProof::ByEquivalenceClass(p))
        }
        EqualFactSearchedProof::ByObjectDefinition(p) => {
            Some(StrictEqualArgProof::ByObjectDefinition(p))
        }
        EqualFactSearchedProof::ByBuiltinStrategy(p) => {
            Some(StrictEqualArgProof::ByBuiltinStrategy(p))
        }
        EqualFactSearchedProof::ByMatchingOneArgByOne(p) => {
            Some(StrictEqualArgProof::ByMatchingOneArgByOne(p))
        }
        EqualFactSearchedProof::ByKnownForallFact(_)
        | EqualFactSearchedProof::ByKnownForallFactViaSymmetry(_)
        | EqualFactSearchedProof::ByBuiltinRewrite(_) => None,
    }
}
