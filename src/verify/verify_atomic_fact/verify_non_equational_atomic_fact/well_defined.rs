use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

impl Runtime {
    pub fn verify_non_equational_atomic_fact_well_definedness2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<AtomicFactWellDefinedProof2, RuntimeError> {
        self.verify_atomic_fact_well_definedness2(fact, verify_state)
    }
}
