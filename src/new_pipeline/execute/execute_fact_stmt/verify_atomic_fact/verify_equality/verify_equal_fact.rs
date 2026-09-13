use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact};
use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    EqualFactSearchedProof, EqualFactSearchedProofByKnownAtomicFact,
    EqualFactSearchedProofByKnownForallFact, VerifyEqualityResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

use super::EqualitySearchProofByBuiltinStrategy;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyEqualityResult> {
        let well_defined_proof = self.verify_atomic_fact_well_definedness(
            &AtomicFact::EqualFact(fact.clone()),
            verify_state.clone(),
        )?;
        let searched_proof = self.search_equal_fact_proof(fact, verify_state)?;
        Ok(VerifyEqualityResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    // Stage order: cache → builtin rule → known atomic → builtin strategy →
    // known forall. Equality algebraic properties are intrinsic.
    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<EqualFactSearchedProof> {
        if let Some(result) = self.search_equal_fact_proof_by_cache(fact, verify_state.clone())? {
            return Ok(EqualFactSearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(EqualFactSearchedProof::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_atomic_fact(fact, verify_state.clone())?
        {
            return Ok(EqualFactSearchedProof::ByKnownAtomicFact(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(EqualFactSearchedProof::ByBuiltinStrategy(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_forall_fact(fact, verify_state.clone())?
        {
            return Ok(EqualFactSearchedProof::ByKnownForallFact(result));
        }

        Err(RuntimeError::Unknown(
            "search_equal_fact_proof: no equality proof found".to_string(),
        ))
    }

    pub fn search_equal_fact_proof_by_cache(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CacheSearchProof>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByKnownAtomicFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinStrategy>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByKnownForallFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
