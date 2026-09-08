use crate::prelude::*;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<VerifyEqualityResult, RuntimeError> {
        let well_defined_result =
            self.verify_equal_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_equal_fact_proof(fact, verify_state)?;
        Ok(VerifyEqualityResult {
            fact: fact.clone(),
            well_defined_result,
            searched_proof,
        })
    }

    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<EqualitySearchedProof, RuntimeError> {
    }
}
