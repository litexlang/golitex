use crate::prelude::*;

impl Runtime {
    pub fn verify_chain_fact(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<VerifyChainFactResult, RuntimeError> {
        let well_defined_result =
            self.verify_chain_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_chain_fact_proof(fact, verify_state)?;
        Ok(VerifyChainFactResult {
            fact: fact.clone(),
            well_defined_result,
            searched_proof,
        })
    }

    pub fn search_chain_fact_proof(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<ChainFactSearchedProof, RuntimeError> {
    }
}
