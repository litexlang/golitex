use crate::prelude::*;

pub struct VerifyChainFactWellDefinednessResult {
    pub well_definedness_of_each_comparison: Vec<VerifyAtomicFactWellDefinednessResult>,
}

impl Runtime {
    pub fn verify_chain_fact_well_definedness(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> Result<VerifyChainFactWellDefinednessResult, RuntimeError> {
    }
}
