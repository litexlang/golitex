use crate::prelude::*;

impl Runtime {
    pub fn verify_not_exist_fact(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<VerifyNotExistFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_not_exist_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_not_exist_fact_proof(fact, verify_state)?;
        Ok(VerifyNotExistFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_not_exist_fact_proof(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<NotExistFactSearchedProof, RuntimeError> {
        if let Some(result) =
            self.search_not_exist_fact_proof_by_cache(fact, verify_state.clone())?
        {
            return Ok(NotExistFactSearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_not_exist_fact_proof_by_demorgan_forall(fact, verify_state)?
        {
            return Ok(NotExistFactSearchedProof::ByDemorganForall(result));
        }

        todo!()
    }

    pub fn search_not_exist_fact_proof_by_cache(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<Option<CacheSearchProof>, RuntimeError> {
    }

    pub fn search_not_exist_fact_proof_by_demorgan_forall(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<Option<VerifyForallFactResult>, RuntimeError> {
    }
}
