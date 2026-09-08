use crate::prelude::*;

impl Runtime {
    pub fn verify_not_exist_fact(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<VerifyNotExistFactResult, RuntimeError> {
        let well_defined_result =
            self.verify_not_exist_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_not_exist_fact_proof(fact, verify_state)?;
        Ok(VerifyNotExistFactResult {
            fact: fact.clone(),
            well_defined_result,
            searched_proof,
        })
    }

    pub fn search_not_exist_fact_proof(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<NotExistFactSearchedProof, RuntimeError> {
    }
}
