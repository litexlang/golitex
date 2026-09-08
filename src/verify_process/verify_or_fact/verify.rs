use crate::prelude::*;

impl Runtime {
    pub fn verify_or_fact(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<VerifyOrFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_or_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_or_fact_proof(fact, verify_state)?;
        Ok(VerifyOrFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_or_fact_proof(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<OrFactSearchedProof, RuntimeError> {
    }
}
