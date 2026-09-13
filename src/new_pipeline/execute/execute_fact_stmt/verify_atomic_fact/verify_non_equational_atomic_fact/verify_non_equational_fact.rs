use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    NonEquationalFactSearchedProof, NonEquationalFactSearchedProofByDefinition,
    NonEquationalFactSearchedProofByKnownAtomicFact,
    NonEquationalFactSearchedProofByKnownForallFact, VerifyNonEquationalFactResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

use super::{
    NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite,
    NonEquationalAtomicFactSearchProofByBuiltinStrategy,
    NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite,
};

impl Runtime {
    pub fn verify_non_equational_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyNonEquationalFactResult> {
        let well_defined_proof =
            self.verify_atomic_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_non_equational_fact_proof(fact, verify_state)?;
        Ok(VerifyNonEquationalFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    // Stage order: cache → builtin rule → known atomic → builtin strategy →
    // known forall → builtin algebraic rewrite → known algebraic rewrite.
    pub fn search_non_equational_fact_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<NonEquationalFactSearchedProof> {
        if let Some(result) =
            self.search_non_equational_fact_proof_by_cache(fact, verify_state.clone())?
        {
            return Ok(NonEquationalFactSearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_non_equational_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(NonEquationalFactSearchedProof::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_non_equational_fact_proof_by_known_atomic_fact(fact, verify_state.clone())?
        {
            return Ok(NonEquationalFactSearchedProof::ByKnownAtomicFact(result));
        }

        if let Some(result) =
            self.search_non_equational_fact_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(NonEquationalFactSearchedProof::ByBuiltinStrategy(result));
        }

        if let Some(result) =
            self.search_non_equational_fact_proof_by_known_forall_fact(fact, verify_state.clone())?
        {
            return Ok(NonEquationalFactSearchedProof::ByKnownForallFact(result));
        }

        if let Some(result) = self.search_non_equational_fact_proof_by_builtin_algebraic_rewrite(
            fact,
            verify_state.clone(),
        )? {
            return Ok(NonEquationalFactSearchedProof::ByBuiltinAlgebraicRewrite(
                result,
            ));
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) = self
                .search_non_equational_fact_proof_by_known_algebraic_rewrite(fact, verify_state)?
            {
                return Ok(NonEquationalFactSearchedProof::ByKnownAlgebraicRewrite(
                    result,
                ));
            }
        }

        Err(RuntimeError::Unknown(
            "search_non_equational_fact_proof: no non-equational proof found".to_string(),
        ))
    }

    pub fn search_non_equational_fact_proof_by_cache(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CacheSearchProof>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalFactSearchedProofByKnownAtomicFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_fact_proof_by_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalFactSearchedProofByDefinition>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinStrategy>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalFactSearchedProofByKnownForallFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_fact_proof_by_builtin_algebraic_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_fact_proof_by_known_algebraic_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
