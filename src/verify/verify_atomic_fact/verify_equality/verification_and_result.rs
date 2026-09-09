use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyEqualityResult2 {
    pub fact: EqualFact,
    pub well_defined_proof: AtomicFactWellDefinedProof2,
    pub searched_proof: EqualitySearchedProof2,
}

pub enum EqualitySearchedProof2 {
    ByCache(CacheSearchProof2),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule2),
    ByKnownAtomicFact(EqualitySearchedProofByKnownAtomicFact2),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy2),
    ByKnownForallFact(EqualitySearchedProofByKnownForallFact2),
    ByBuiltinAlgebraicRewrite(EqualitySearchProofByBuiltinAlgebraicRewrite2),
    ByKnownAlgebraicRewrite(EqualitySearchProofByKnownAlgebraicRewrite2),
}

pub struct EqualitySearchedProofByKnownAtomicFact2 {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult2>,
}

pub struct EqualitySearchedProofByKnownForallFact2 {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_equal_fact2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyEqualityResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_equal_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = self.search_equal_fact_proof2(fact, verify_state)?;
        Ok(VerifyEqualityResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_equal_fact_proof2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<EqualitySearchedProof2, RuntimeError> {
        if let Some(result) =
            self.search_equal_fact_proof_by_cache2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByCache(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_rule2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_atomic_fact2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByKnownAtomicFact(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_strategy2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByBuiltinStrategy(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_forall_fact2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByKnownForallFact(result));
        }

        if let Some(result) = self
            .search_equal_fact_proof_by_builtin_algebraic_rewrite2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByBuiltinAlgebraicRewrite(result));
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) =
                self.search_equal_fact_proof_by_known_algebraic_rewrite2(fact, verify_state)?
            {
                return Ok(EqualitySearchedProof2::ByKnownAlgebraicRewrite(result));
            }
        }

        todo!()
    }

    pub fn search_equal_fact_proof_by_cache2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<Option<CacheSearchProof2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by cache")
    }

    pub fn search_equal_fact_proof_by_builtin_rule2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<Option<EqualitySearchProofByBuiltinRule2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by builtin rule")
    }

    pub fn search_equal_fact_proof_by_known_atomic_fact2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<Option<EqualitySearchedProofByKnownAtomicFact2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by known atomic fact")
    }

    pub fn search_equal_fact_proof_by_builtin_strategy2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<Option<EqualitySearchProofByBuiltinStrategy2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by builtin strategy")
    }

    pub fn search_equal_fact_proof_by_known_forall_fact2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<Option<EqualitySearchedProofByKnownForallFact2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by known forall fact")
    }

    pub fn search_equal_fact_proof_by_builtin_algebraic_rewrite2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<Option<EqualitySearchProofByBuiltinAlgebraicRewrite2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by builtin algebraic rewrite")
    }

    pub fn search_equal_fact_proof_by_known_algebraic_rewrite2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> Result<Option<EqualitySearchProofByKnownAlgebraicRewrite2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by known algebraic rewrite")
    }
}
