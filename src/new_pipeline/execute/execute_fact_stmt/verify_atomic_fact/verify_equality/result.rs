use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualitySearchProofByBuiltinRewrite, EqualitySearchProofByBuiltinRule,
    EqualitySearchProofByBuiltinStrategy, EqualitySearchProofByKnownRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::runtime_ids::FactId;

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
    ByKnownForallFact(SearchProofByKnownForallFact),
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
