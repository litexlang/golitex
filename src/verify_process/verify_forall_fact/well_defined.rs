use crate::prelude::*;

pub enum VerifyExistOrAndChainAtomicFactWellDefinednessResult {
    AtomicFact(VerifyAtomicFactWellDefinednessResult),
    AndFact(VerifyAndFactWellDefinednessResult),
    ChainFact(VerifyChainFactWellDefinednessResult),
    OrFact(VerifyOrFactWellDefinednessResult),
    ExistFact(VerifyExistFactWellDefinednessResult),
}

pub struct VerifyForallFactWellDefinednessResult {
    pub well_definedness_of_each_premise: Vec<VerifyExistOrAndChainAtomicFactWellDefinednessResult>,
    pub well_definedness_of_each_then_fact: Vec<VerifyExistOrAndChainAtomicFactWellDefinednessResult>,
}

impl Runtime {
    pub fn verify_forall_fact_well_definedness(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<VerifyForallFactWellDefinednessResult, RuntimeError> {
    }

    pub fn verify_exist_or_and_chain_atomic_fact_well_definedness(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: VerifyState,
    ) -> Result<VerifyExistOrAndChainAtomicFactWellDefinednessResult, RuntimeError> {
    }
}
