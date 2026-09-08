use crate::prelude::*;

pub enum VerifyAndChainAtomicFactWellDefinednessResult {
    AtomicFact(VerifyAtomicFactWellDefinednessResult),
    AndFact(VerifyAndFactWellDefinednessResult),
    ChainFact(VerifyChainFactWellDefinednessResult),
}

pub struct VerifyOrFactWellDefinednessResult {
    pub well_definedness_of_each_branch: Vec<VerifyAndChainAtomicFactWellDefinednessResult>,
}

impl Runtime {
    pub fn verify_or_fact_well_definedness(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> Result<VerifyOrFactWellDefinednessResult, RuntimeError> {
    }

    pub fn verify_and_chain_atomic_fact_well_definedness(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: VerifyState,
    ) -> Result<VerifyAndChainAtomicFactWellDefinednessResult, RuntimeError> {
    }
}
