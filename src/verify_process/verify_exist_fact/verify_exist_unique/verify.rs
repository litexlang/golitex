use crate::prelude::*;

impl Runtime {
    pub fn verify_exist_unique_fact(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<VerifyExistUniqueFactResult, RuntimeError> {
        let well_defined_result =
            self.verify_exist_unique_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_exist_unique_fact_proof(fact, verify_state)?;
        Ok(VerifyExistUniqueFactResult {
            fact: fact.clone(),
            well_defined_result,
            searched_proof,
        })
    }

    pub fn search_exist_unique_fact_proof(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<ExistUniqueFactSearchedProof, RuntimeError> {
    }
}
