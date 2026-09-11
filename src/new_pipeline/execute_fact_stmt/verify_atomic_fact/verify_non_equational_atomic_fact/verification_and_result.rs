use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyNonEquationalAtomicFactResult2 {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof2,
    pub searched_proof: NonEquationalAtomicFactSearchedProof2,
}

pub enum NonEquationalAtomicFactSearchedProof2 {
    ByCache(CacheSearchProof2),
    ByBuiltinRule(NonEquationalAtomicFactSearchProofByBuiltinRule2),
    ByKnownAtomicFact(NonEquationalAtomicFactSearchedProofByKnownAtomicFact2),
    ByDefinition(NonEquationalAtomicFactSearchedProofByDefinition2),
    ByBuiltinStrategy(NonEquationalAtomicFactSearchProofByBuiltinStrategy2),
    ByKnownForallFact(NonEquationalAtomicFactSearchedProofByKnownForallFact2),
    ByBuiltinAlgebraicRewrite(NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2),
    ByKnownAlgebraicRewrite(NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2),
}

pub struct NonEquationalAtomicFactSearchedProofByKnownAtomicFact2 {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult2>,
}

pub struct NonEquationalAtomicFactSearchedProofByDefinition2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

// Record how forall params map to goal args, e.g. forall a R: a > 0 => $p(a) vs $p(1) maps a -> 1.
pub struct NonEquationalAtomicFactSearchedProofByKnownForallFact2 {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    // Proofs that matched args satisfy param types and domain facts, e.g. 1 $in R and 1 > 0 for $p(1).
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_non_equational_atomic_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyNonEquationalAtomicFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_atomic_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = self.search_non_equational_atomic_fact_proof2(fact, verify_state)?;
        Ok(VerifyNonEquationalAtomicFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_non_equational_atomic_fact_proof2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<NonEquationalAtomicFactSearchedProof2, RuntimeError> {
        if let Some(result) =
            self.search_non_equational_atomic_proof_by_cache2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByCache(result));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_rule2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByBuiltinRule(result));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_atomic_fact2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByKnownAtomicFact(
                result,
            ));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_definition2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByDefinition(result));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_builtin_strategy2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByBuiltinStrategy(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_forall_fact2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByKnownForallFact(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_builtin_algebraic_rewrite2(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByBuiltinAlgebraicRewrite(result));
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) = self
                .search_non_equational_atomic_proof_by_known_algebraic_rewrite2(
                    fact,
                    verify_state,
                )?
            {
                return Ok(NonEquationalAtomicFactSearchedProof2::ByKnownAlgebraicRewrite(result));
            }
        }

        todo!()
    }

    pub fn search_non_equational_atomic_proof_by_cache2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<CacheSearchProof2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by cache")
    }

    pub fn search_non_equational_atomic_proof_by_builtin_rule2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinRule2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by builtin rule")
    }

    pub fn search_non_equational_atomic_proof_by_known_atomic_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByKnownAtomicFact2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known atomic fact")
    }

    pub fn search_non_equational_atomic_proof_by_definition2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByDefinition2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by definition")
    }

    pub fn search_non_equational_atomic_proof_by_builtin_strategy2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinStrategy2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by builtin strategy")
    }

    pub fn search_non_equational_atomic_proof_by_known_forall_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByKnownForallFact2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known forall fact")
    }

    pub fn search_non_equational_atomic_proof_by_builtin_algebraic_rewrite2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2>, RuntimeError>
    {
        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_order_dual2(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2::OrderDual(result),
            ));
        }

        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_order_dual2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinOrderDual2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by builtin order dual")
    }

    pub fn search_non_equational_atomic_proof_by_known_algebraic_rewrite2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2>, RuntimeError>
    {
        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_reflexivity2(fact, verify_state.clone())?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2::Reflexivity(result),
            ));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_known_symmetry2(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2::Symmetry(result),
            ));
        }

        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_reflexivity2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByKnownReflexivity2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known reflexivity")
    }

    pub fn search_non_equational_atomic_proof_by_known_symmetry2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByKnownSymmetry2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known symmetry")
    }
}
