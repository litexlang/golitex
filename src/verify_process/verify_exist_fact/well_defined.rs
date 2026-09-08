use crate::prelude::*;

pub enum VerifyQuantifierFreeFactWellDefinednessResult {
    AtomicFact(VerifyAtomicFactWellDefinednessResult),
    AndFact(VerifyAndFactWellDefinednessResult),
    ChainFact(VerifyChainFactWellDefinednessResult),
    OrFact(VerifyOrFactWellDefinednessResult),
}

pub struct VerifyExistFactWellDefinednessResult {
    pub well_definedness_of_each_body_fact: Vec<VerifyQuantifierFreeFactWellDefinednessResult>,
}

impl Runtime {
    pub fn verify_exist_fact_well_definedness(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<VerifyExistFactWellDefinednessResult, RuntimeError> {
    }

    pub fn verify_quantifier_free_fact_well_definedness(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: VerifyState,
    ) -> Result<VerifyQuantifierFreeFactWellDefinednessResult, RuntimeError> {
    }
}
