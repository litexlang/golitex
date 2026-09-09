use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct AndFactWellDefinedProof2 {
    pub well_defined_of_each_conjunct: Vec<AtomicFactWellDefinedProof2>,
}

impl Runtime {
    pub fn verify_and_fact_well_definedness2(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState2,
    ) -> Result<AndFactWellDefinedProof2, RuntimeError> {
        let mut well_defined_of_each_conjunct = Vec::new();
        for conjunct in fact.facts.iter() {
            well_defined_of_each_conjunct
                .push(self.verify_atomic_fact_well_definedness2(conjunct, verify_state.clone())?);
        }
        Ok(AndFactWellDefinedProof2 {
            well_defined_of_each_conjunct,
        })
    }
}
