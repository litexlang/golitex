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

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<VerifyEqualityResult, RuntimeError> {
        let well_defined_proof =
            self.verify_equal_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_equal_fact_proof(fact, verify_state)?;
        Ok(VerifyEqualityResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<EqualitySearchedProof, RuntimeError> {
    }
}
