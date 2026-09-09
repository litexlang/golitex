use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<AtomicFactWellDefinedProof, RuntimeError> {
        self.verify_atomic_fact_well_definedness(fact, verify_state)
    }
}
