use crate::prelude::*;

pub struct VerifyChainFactResult {
    pub fact: ChainFact,
    pub well_defined_proof: ChainFactWellDefinedProof,
    pub searched_proof: ChainFactSearchedProof,
}

pub struct ChainFactSearchedProof {
    pub proof_of_each_edge: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn verify_chain_fact(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<VerifyChainFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_chain_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_chain_fact_proof(fact, verify_state)?;
        Ok(VerifyChainFactResult {
            fact: fact.clone(),
            well_defined_proof,
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
