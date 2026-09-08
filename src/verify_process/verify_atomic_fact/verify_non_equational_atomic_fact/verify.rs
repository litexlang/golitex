use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<VerifyNonEquationalAtomicFactResult, RuntimeError> {
        let well_defined_result =
            self.verify_non_equational_atomic_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_non_equational_atomic_fact_proof(fact, verify_state)?;
        Ok(VerifyNonEquationalAtomicFactResult {
            fact: fact.clone(),
            well_defined_result,
            searched_proof,
        })
    }

    pub fn search_non_equational_atomic_fact_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<NonEquationalAtomicFactSearchedProof, RuntimeError> {
        if let Some(result) =
            self.search_non_equational_atomic_proof_by_cache(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByBuiltinRule(result));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_atomic_fact(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByKnownAtomicFact(result));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_definition(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByDefinition(result));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByBuiltinStrategy(result));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_forall_fact(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByKnownForallFact(result));
        }

        if let Some(result) = self.search_non_equational_atomic_proof_by_builtin_algebraic_rewrite(
            fact,
            verify_state.clone(),
        )? {
            return Ok(NonEquationalAtomicFactSearchedProof::ByBuiltinAlgebraicRewrite(
                result,
            ));
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) = self
                .search_non_equational_atomic_proof_by_known_algebraic_rewrite(fact, verify_state)?
            {
                return Ok(NonEquationalAtomicFactSearchedProof::ByKnownAlgebraicRewrite(
                    result,
                ));
            }
        }

        todo!()
    }

    pub fn search_non_equational_atomic_proof_by_cache(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<CacheSearchProof>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_builtin_rule(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinRule>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByKnownAtomicFact>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByDefinition>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_builtin_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinStrategy>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_known_forall_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByKnownForallFact>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_builtin_algebraic_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite>, RuntimeError>
    {
        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_order_dual(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite::OrderDual(result),
            ));
        }

        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_order_dual(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinOrderDual>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_known_algebraic_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite>, RuntimeError>
    {
        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_reflexivity(fact, verify_state.clone())?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite::Reflexivity(result),
            ));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_known_symmetry(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite::Symmetry(result),
            ));
        }

        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_reflexivity(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByKnownReflexivity>, RuntimeError> {
    }

    pub fn search_non_equational_atomic_proof_by_known_symmetry(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByKnownSymmetry>, RuntimeError> {
    }
}
