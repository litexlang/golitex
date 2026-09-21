use crate::new_pipeline::ast::fact::{EqualFact, Fact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualitySearchProofByBuiltinRewrite, EqualitySearchProofByBuiltinRule,
    EqualitySearchProofByBuiltinStrategy, EqualitySearchProofByObjectDefinition,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_matching_one_arg_by_one::EqualFactSearchedProofByMatchingOneArgByOne;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::{
    EqualFactWellDefinedProof, FailToVerifyEqualFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::runtime_ids::{FactId, IdentifierId};

// Shared known-forall application certificate.
// Field order mirrors successful apply stages:
// match args → prove param-type + dom requirements.
// `arg_match_proofs` is one entry per conclusion/goal arg (Lean-aligned).
// Boxed under EqualFactSearchedProof::ByKnownForallFact to break the type cycle.
pub struct SearchProofByKnownForallFact {
    pub cite: crate::new_pipeline::exec_env::ForallConclusionCite,
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
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownEquality(EqualFactSearchedProofByKnownEquality),
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
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownEquality(EqualFactSearchedProofByKnownEquality),
    ByObjectDefinition(EqualitySearchProofByObjectDefinition),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByMatchingOneArgByOne(EqualFactSearchedProofByMatchingOneArgByOne),
    ByKnownForallFact(Box<SearchProofByKnownForallFact>),
    // Legacy: match known forall on the swapped equality, then cite symmetry.
    // Example: known `forall x: f(c, x) = x`, goal `t = f(c, t)`.
    ByKnownForallFactViaSymmetry(Box<EqualFactSearchedProofByKnownForallViaSymmetry>),
    ByBuiltinRewrite(EqualitySearchProofByBuiltinRewrite),
}

// Prove `L = R` by proving `R = L` via known forall, then equality symmetry.
pub struct EqualFactSearchedProofByKnownForallViaSymmetry {
    pub reversed_equal: EqualFact,
    pub known_forall: SearchProofByKnownForallFact,
}

// Oriented cite chain from goal.left to goal.right over generating equality
// edges only. Each entry: (from, to, cited_equal_fact_id). Empty <=> reflexive.
// FactIds must come from KnownEqualityMemory.generating_edges, never from a
// class-id handle alone.
pub struct EqualFactSearchedProofByKnownEquality {
    pub path: Vec<(Obj, Obj, FactId)>,
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
        EqualFactSearchedProof::ByBuiltinRule(p) => Some(StrictEqualArgProof::ByBuiltinRule(p)),
        EqualFactSearchedProof::ByKnownEquality(p) => {
            Some(StrictEqualArgProof::ByKnownEquality(p))
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
