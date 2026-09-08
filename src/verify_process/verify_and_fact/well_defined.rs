use crate::prelude::*;

pub struct VerifyAndFactWellDefinednessResult {
    pub well_definedness_of_each_conjunct: Vec<VerifyAtomicFactWellDefinednessResult>,
}

impl Runtime {
    pub fn verify_and_fact_well_definedness(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> Result<VerifyAndFactWellDefinednessResult, RuntimeError> {
    }
}
