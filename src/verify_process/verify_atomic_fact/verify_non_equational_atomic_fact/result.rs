use crate::prelude::*;

pub struct VerifyNonEquationalAtomicFactResult {
    pub well_definedness_result: VerifyNonEquationalAtomicFactWellDefinednessResult,
    pub search_proof: NonEquationalAtomicFactSearchProof,
}

pub struct VerifyNonEquationalAtomicFactWellDefinednessResult {
    pub well_definedness_proof_of_each_parameter: Vec<WellDefinednessProofOfObj>,
}

pub enum NonEquationalAtomicFactSearchProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(NonEquationalAtomicFactSearchProofByBuiltinRule),
    ByKnownAtomicFact(NonEquationalAtomicFactSearchProofByKnownAtomicFact),
    ByDefinition(NonEquationalAtomicFactSearchProofByDefinition),
    ByBuiltinStrategy(NonEquationalAtomicFactSearchProofByBuiltinStrategy),
    ByKnownForallFact(NonEquationalAtomicFactSearchProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite),
}

pub enum NonEquationalAtomicFactSearchProofByBuiltinRule {
    // ...
}

pub struct NonEquationalAtomicFactSearchProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct NonEquationalAtomicFactSearchProofByDefinition {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct NonEquationalAtomicFactSearchProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
