use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualitySearchProofByBuiltinRule, EqualitySearchProofByBuiltinStrategy,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByBuiltinAlgebraicRewrite,
    AtomicExceptEqualityFactSearchProofByBuiltinRule, AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
    AtomicExceptEqualityFactSearchProofByKnownAlgebraicRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_well_defined::AtomicFactWellDefinedProof;
use crate::new_pipeline::runtime::runtime_ids::FactId;

pub struct VerifyEqualityResult {
    pub fact: EqualFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: EqualFactSearchedProof,
}

// Mirrors search_equal_fact_proof stage order.
// Equality algebraic properties are intrinsic to equality search, so there is
// no separate algebraic-rewrite stage.
pub enum EqualFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownEquality(EqualFactSearchedProofByKnownEquality),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByKnownForallFact(EqualFactSearchedProofByKnownForallFact),
}

// Oriented cite chain from goal.left to goal.right over generating equality
// edges only. Each entry: (from, to, cited_equal_fact_id). Empty <=> reflexive.
// FactIds must come from KnownEqualityMemory.generating_edges, never from a
// class-id handle alone.
pub struct EqualFactSearchedProofByKnownEquality {
    pub path: Vec<(Obj, Obj, FactId)>,
}

pub struct EqualFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct VerifyAtomicExceptEqualityFactResult {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: AtomicExceptEqualityFactSearchedProof,
}

// Mirrors search_atomic_except_equality_fact_proof stage order.
pub enum AtomicExceptEqualityFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule),
    ByKnownAtomicFact(AtomicExceptEqualityFactSearchProofByKnownAtomicFact),
    ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy),
    ByDefinition(AtomicExceptEqualityFactSearchProofByDefinition),
    ByKnownForallFact(AtomicExceptEqualityFactSearchProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(AtomicExceptEqualityFactSearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(AtomicExceptEqualityFactSearchProofByKnownAlgebraicRewrite),
}

pub struct AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    // One ByKnownEquality path per argument (empty path when keys already match).
    pub why_parameters_of_known_fact_are_equal_to_givens:
        Vec<EqualFactSearchedProofByKnownEquality>,
}

pub struct AtomicExceptEqualityFactSearchProofByDefinition {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct AtomicExceptEqualityFactSearchProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
