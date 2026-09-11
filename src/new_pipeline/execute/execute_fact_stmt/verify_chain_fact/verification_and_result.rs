use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyChainFactResult2 {
    pub fact: ChainFact,
    pub well_defined_proof: ChainFactWellDefinedProof2,

    // Prove every adjacent comparison in source order. Keep the child proofs on
    // the outer result so a consumer can follow the complete chain proof.
    pub proof_of_each_edge: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_chain_fact2(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyChainFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_chain_fact_well_definedness2(fact, verify_state.clone())?;
        let proof_of_each_edge = self.search_chain_fact_proof2(fact, verify_state)?;
        Ok(VerifyChainFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            proof_of_each_edge,
        })
    }

    // Expand the chain into adjacent atomic comparisons and prove each one.
    pub fn search_chain_fact_proof2(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState2,
    ) -> Result<Vec<VerifyFactResult2>, RuntimeError> {
        let edges = fact.facts()?;
        let mut proof_of_each_edge = Vec::new();
        for edge in edges.iter() {
            proof_of_each_edge.push(VerifyFactResult2::AtomicFact(
                self.verify_atomic_fact2(edge, verify_state.clone())?,
            ));
        }
        Ok(proof_of_each_edge)
    }
}
