use crate::prelude::*;

pub struct VerifyNonEquationalAtomicFactResult {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof,
    pub searched_proof: NonEquationalAtomicFactSearchedProof,
}

pub enum NonEquationalAtomicFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(NonEquationalAtomicFactSearchProofByBuiltinRule),
    ByKnownAtomicFact(NonEquationalAtomicFactSearchedProofByKnownAtomicFact),
    ByDefinition(NonEquationalAtomicFactSearchedProofByDefinition),
    ByBuiltinStrategy(NonEquationalAtomicFactSearchProofByBuiltinStrategy),
    ByKnownForallFact(NonEquationalAtomicFactSearchedProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite),
}

pub struct NonEquationalAtomicFactSearchedProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct NonEquationalAtomicFactSearchedProofByDefinition {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Record how forall params map to goal args, e.g. forall a R: a > 0 => $p(a) vs $p(1) maps a -> 1.
pub struct NonEquationalAtomicFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    // Proofs that matched args satisfy param types and domain facts, e.g. 1 $in R and 1 > 0 for $p(1).
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn verify_non_equational_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<VerifyNonEquationalAtomicFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_non_equational_atomic_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_non_equational_atomic_fact_proof(fact, verify_state)?;
        Ok(VerifyNonEquationalAtomicFactResult {
            fact: fact.clone(),
            well_defined_proof,
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
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by cache")
    }

    pub fn search_non_equational_atomic_proof_by_builtin_rule(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinRule>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by builtin rule")
    }

    pub fn search_non_equational_atomic_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByKnownAtomicFact>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known atomic fact")
    }

    pub fn search_non_equational_atomic_proof_by_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByDefinition>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by definition")
    }

    pub fn search_non_equational_atomic_proof_by_builtin_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByBuiltinStrategy>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by builtin strategy")
    }

    pub fn search_non_equational_atomic_proof_by_known_forall_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchedProofByKnownForallFact>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known forall fact")
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
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by builtin order dual")
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
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known reflexivity")
    }

    pub fn search_non_equational_atomic_proof_by_known_symmetry(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<Option<NonEquationalAtomicFactSearchProofByKnownSymmetry>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search non-equational atomic by known symmetry")
    }
}
