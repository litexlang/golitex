use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct VerifyChainFactResult {
    pub fact: ChainFact,
    pub well_defined_proof: ChainFactWellDefinedProof,

    // Prove every adjacent comparison in source order. Keep the child proofs on
    // the outer result so a consumer can follow the complete chain proof.
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
            proof_of_each_edge.push(VerifyFactResult::AtomicFact(
                self.verify_atomic_fact(edge, verify_state.clone())?,
            ));
        }
        Ok(proof_of_each_edge)
    }
}
