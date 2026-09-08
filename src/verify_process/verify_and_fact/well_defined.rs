use crate::prelude::*;

pub struct AndFactWellDefinedProof {
    pub well_defined_of_each_conjunct: Vec<AtomicFactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_and_fact_well_definedness(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> Result<AndFactWellDefinedProof, RuntimeError> {
    }
}
