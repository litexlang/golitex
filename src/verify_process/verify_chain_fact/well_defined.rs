use crate::prelude::*;

pub struct ChainFactWellDefinedProof {
    pub well_defined_of_each_comparison: Vec<AtomicFactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_chain_fact_well_definedness(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<ChainFactWellDefinedProof, RuntimeError> {
    }
}
