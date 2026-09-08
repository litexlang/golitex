use crate::prelude::*;

impl Runtime {
    pub fn verify_and_fact(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> Result<VerifyAndFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_and_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_and_fact_proof(fact, verify_state)?;
        Ok(VerifyAndFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_and_fact_proof(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> Result<AndFactSearchedProof, RuntimeError> {
    }
}
