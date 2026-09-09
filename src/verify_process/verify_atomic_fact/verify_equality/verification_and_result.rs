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
        if let Some(result) =
            self.search_equal_fact_proof_by_cache(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_atomic_fact(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof::ByKnownAtomicFact(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof::ByBuiltinStrategy(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_forall_fact(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof::ByKnownForallFact(result));
        }

        if let Some(result) = self
            .search_equal_fact_proof_by_builtin_algebraic_rewrite(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof::ByBuiltinAlgebraicRewrite(result));
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) =
                self.search_equal_fact_proof_by_known_algebraic_rewrite(fact, verify_state)?
            {
                return Ok(EqualitySearchedProof::ByKnownAlgebraicRewrite(result));
            }
        }

        todo!()
    }

    pub fn search_equal_fact_proof_by_cache(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<Option<CacheSearchProof>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by cache")
    }

    pub fn search_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<Option<EqualitySearchProofByBuiltinRule>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by builtin rule")
    }

    pub fn search_equal_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<Option<EqualitySearchedProofByKnownAtomicFact>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by known atomic fact")
    }

    pub fn search_equal_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<Option<EqualitySearchProofByBuiltinStrategy>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by builtin strategy")
    }

    pub fn search_equal_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<Option<EqualitySearchedProofByKnownForallFact>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by known forall fact")
    }

    pub fn search_equal_fact_proof_by_builtin_algebraic_rewrite(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<Option<EqualitySearchProofByBuiltinAlgebraicRewrite>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by builtin algebraic rewrite")
    }

    pub fn search_equal_fact_proof_by_known_algebraic_rewrite(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<Option<EqualitySearchProofByKnownAlgebraicRewrite>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search equal fact by known algebraic rewrite")
    }
}
