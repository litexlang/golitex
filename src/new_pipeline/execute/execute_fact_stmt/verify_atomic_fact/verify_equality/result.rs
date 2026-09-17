use crate::new_pipeline::ast::fact::{EqualFact, Fact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualitySearchProofByBuiltinRewrite, EqualitySearchProofByBuiltinRule,
    EqualitySearchProofByBuiltinStrategy, EqualitySearchProofByKnownRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::runtime_ids::{FactId, IdentifierId};

// Shared known-forall application certificate.
// Field order mirrors successful apply stages: match args → requirements.
// `arg_match_proofs` is one entry per conclusion/goal arg (Lean-aligned).
// Boxed under EqualFactSearchedProof::ByKnownForallFact to break the type cycle.
pub struct SearchProofByKnownForallFact {
    pub cite: crate::new_pipeline::exec_env::ForallConclusionCite,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Output of matching conclusion args to goal args (before dom requirements).
pub struct MatchForallConclusionArgsProof {
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
}

// One slot per (pattern_arg, goal_arg). Length equals arg arity.
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
    // Pattern is not a forall param: prove pattern = goal_arg under strict equal.
    NonParamEqual {
        pattern: Obj,
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
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
}

pub enum VerifyEqualityResult {
    Success(VerifyEqualitySuccess),
    Failed(VerifyEqualityFailed),
}

pub struct VerifyEqualitySuccess {
    pub fact: EqualFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: EqualFactSearchedProof,
}

pub enum VerifyEqualityFailed {
    FailToVerifyWellDefined(FailToVerifyAtomicFactWellDefinedResult),
    FailToSearchProof {
        fact: EqualFact,
        well_defined_proof: AtomicFactWellDefinedProof,
    },
}

impl VerifyEqualityResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// Mirrors search_equal_fact_proof stage order.
// Rewrite stages replace legacy opaque resolve_obj: rewrites must be
// explicit certificates (see ByBuiltinRewrite / ByKnownRewrite).
pub enum EqualFactSearchedProof {
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownEquality(EqualFactSearchedProofByKnownEquality),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByKnownForallFact(Box<SearchProofByKnownForallFact>),
    ByBuiltinRewrite(EqualitySearchProofByBuiltinRewrite),
    ByKnownRewrite(EqualitySearchProofByKnownRewrite),
}

// Oriented cite chain from goal.left to goal.right over generating equality
// edges only. Each entry: (from, to, cited_equal_fact_id). Empty <=> reflexive.
// FactIds must come from KnownEqualityMemory.generating_edges, never from a
// class-id handle alone.
pub struct EqualFactSearchedProofByKnownEquality {
    pub path: Vec<(Obj, Obj, FactId)>,
}

pub fn equal_fact_result_from_wd_fail(
    reason: FailToVerifyAtomicFactWellDefinedResult,
) -> VerifyFactResult {
    VerifyFactResult::Equality(Box::new(VerifyEqualityResult::Failed(
        VerifyEqualityFailed::FailToVerifyWellDefined(reason),
    )))
}

pub fn equal_fact_result_from_search_fail(
    fact: &EqualFact,
    well_defined_proof: AtomicFactWellDefinedProof,
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
    well_defined_proof: AtomicFactWellDefinedProof,
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
        EqualFactSearchedProof::ByBuiltinStrategy(p) => {
            Some(StrictEqualArgProof::ByBuiltinStrategy(p))
        }
        EqualFactSearchedProof::ByKnownForallFact(_)
        | EqualFactSearchedProof::ByBuiltinRewrite(_)
        | EqualFactSearchedProof::ByKnownRewrite(_) => None,
    }
}
