use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    EqualFactSearchedProof, EqualFactSearchedProofByKnownForallFact, VerifyEqualityResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::{
    UnknownVerifyFactResult, VerifyFactResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::EqualitySearchProofByBuiltinStrategy;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof = self.verify_atomic_fact_well_definedness(
            &(fact.clone().into()),
            verify_state.clone(),
        )?;
        match self.search_equal_fact_proof(fact, verify_state)? {
            Some(searched_proof) => {
                Ok(VerifyFactResult::Equality(Box::new(VerifyEqualityResult {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                })))
            }
            None => Ok(VerifyFactResult::Unknown(
                UnknownVerifyFactResult::UnableToSearchProof,
            )),
        }
    }

    // Stage order: cache → builtin rule → known equality → builtin strategy →
    // known forall. Equality algebraic properties are intrinsic.
    // Ok(None) means no proof found; that is not a runtime error.
    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        if let Some(result) = self.search_equal_fact_proof_by_cache(fact, verify_state.clone())? {
            return Ok(Some(EqualFactSearchedProof::ByCache(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinRule(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_equality(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByKnownEquality(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinStrategy(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_forall_fact(fact, verify_state)?
        {
            return Ok(Some(EqualFactSearchedProof::ByKnownForallFact(result)));
        }

        Ok(None)
    }

    pub fn search_equal_fact_proof_by_cache(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CacheSearchProof>> {
        let _ = verify_state;
        Ok(self.search_atomic_fact_proof_by_cache(&(fact.clone().into())))
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
