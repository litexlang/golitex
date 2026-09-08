use crate::prelude::*;

pub struct VerifyNonEquationalAtomicFactWellDefinednessResult {
    pub well_definedness_proof_of_each_parameter: Vec<WellDefinednessProofOfObj>,
}

impl Runtime {
    pub fn verify_non_equational_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<VerifyNonEquationalAtomicFactWellDefinednessResult, RuntimeError> {
    }
}
