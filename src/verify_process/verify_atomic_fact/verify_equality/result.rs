use crate::prelude::*;

pub struct VerifyEqualityResult {
    pub well_definedness_result: VerifyAtomicFactWellDefinednessResult,
    pub search_proof: EqualitySearchProof,
}

pub enum EqualitySearchProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownAtomicFact(EqualitySearchProofByKnownAtomicFact),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByKnownForallFact(EqualitySearchProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(EqualitySearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(EqualitySearchProofByKnownAlgebraicRewrite),
}

pub struct EqualitySearchProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct EqualitySearchProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
