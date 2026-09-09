use crate::prelude::*;

impl Runtime {
    pub fn verify_equal_fact_well_definedness(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> Result<AtomicFactWellDefinedProof, RuntimeError> {
        self.verify_atomic_fact_well_definedness(&fact.clone().into(), verify_state)
    }
}
