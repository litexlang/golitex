use crate::prelude::*;

pub struct VerifyEqualityResult {
    pub fact: EqualFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: EqualitySearchedProof,
}

pub enum EqualitySearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownAtomicFact(EqualitySearchedProofByKnownAtomicFact),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByKnownForallFact(EqualitySearchedProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(EqualitySearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(EqualitySearchProofByKnownAlgebraicRewrite),
}

pub struct EqualitySearchedProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct EqualitySearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
