use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualitySearchProofByBuiltinAlgebraicRewrite, EqualitySearchProofByBuiltinRule,
    EqualitySearchProofByBuiltinStrategy, EqualitySearchProofByKnownAlgebraicRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_non_equational_atomic_fact::{
    NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite,
    NonEquationalAtomicFactSearchProofByBuiltinRule,
    NonEquationalAtomicFactSearchProofByBuiltinStrategy,
    NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_well_defined::AtomicFactWellDefinedProof;
use crate::new_pipeline::runtime::runtime_ids::FactId;

pub enum VerifyAtomicFactResult {
    Equality(VerifyEqualityResult),
    NonEquational(VerifyNonEquationalFactResult),
}

pub struct VerifyEqualityResult {
    pub fact: EqualFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: EqualFactSearchedProof,
}

// Mirrors search_equal_fact_proof stage order.
pub enum EqualFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownAtomicFact(EqualFactSearchedProofByKnownAtomicFact),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByKnownForallFact(EqualFactSearchedProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(EqualitySearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(EqualitySearchProofByKnownAlgebraicRewrite),
}

pub struct EqualFactSearchedProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct EqualFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct VerifyNonEquationalFactResult {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: NonEquationalFactSearchedProof,
}

// Mirrors search_non_equational_fact_proof stage order.
pub enum NonEquationalFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(NonEquationalAtomicFactSearchProofByBuiltinRule),
    ByKnownAtomicFact(NonEquationalFactSearchedProofByKnownAtomicFact),
    ByDefinition(NonEquationalFactSearchedProofByDefinition),
    ByBuiltinStrategy(NonEquationalAtomicFactSearchProofByBuiltinStrategy),
    ByKnownForallFact(NonEquationalFactSearchedProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite),
}

pub struct NonEquationalFactSearchedProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct NonEquationalFactSearchedProofByDefinition {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct NonEquationalFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
