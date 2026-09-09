use crate::prelude::*;

impl Runtime {
    pub fn verify_exist_unique_fact(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<VerifyExistUniqueFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_exist_unique_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_exist_unique_fact_proof(fact, verify_state)?;
        Ok(VerifyExistUniqueFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_exist_unique_fact_proof(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<ExistUniqueFactSearchedProof, RuntimeError> {
        if let Some(result) =
            self.search_exist_unique_fact_proof_by_cache(fact, verify_state.clone())?
        {
            return Ok(ExistUniqueFactSearchedProof::ByCache(result));
        }

        if let Some(result) = self
            .search_exist_unique_fact_proof_by_exist_and_uniqueness(fact, verify_state)?
        {
            return Ok(ExistUniqueFactSearchedProof::ProveAsExistFactWithUniqueness(
                result,
            ));
        }

        todo!()
    }

    pub fn search_exist_unique_fact_proof_by_cache(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<Option<CacheSearchProof>, RuntimeError> {
    }

    pub fn search_exist_unique_fact_proof_by_exist_and_uniqueness(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<Option<ExistUniqueFactSearchedProofByExistAndUniqueness>, RuntimeError> {
    }
}
