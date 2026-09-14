use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

use super::verify_chain_fact_result::VerifyChainFactResult;

impl Runtime {
    pub fn verify_chain_fact(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<VerifyChainFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_chain_fact_well_definedness(fact, verify_state.clone())?;
        let proof_of_each_edge = self.search_chain_fact_proof(fact, verify_state)?;
        Ok(VerifyChainFactResult {
            fact: fact.clone(),
            well_defined_proof,
            proof_of_each_edge,
        })
    }

    // Expand the chain into adjacent atomic comparisons and prove each one.
    pub fn search_chain_fact_proof(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<Vec<VerifyFactResult>, RuntimeError> {
        let edges = fact.facts()?;
        let mut proof_of_each_edge = Vec::new();
        for edge in edges.iter() {
            let proof = self.verify_atomic_fact(edge, verify_state.clone())?;
            if proof.is_unknown() {
                return Ok(vec![proof]);
            }
            proof_of_each_edge.push(proof);
        }
        Ok(proof_of_each_edge)
    }
}
