use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct AtomicFactWellDefinedProof2 {
    pub well_defined_of_each_parameter: Vec<WellDefinednessProofOfObj2>,
}

impl Runtime {
    pub fn verify_atomic_fact_well_definedness2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<AtomicFactWellDefinedProof2, RuntimeError> {
        let mut well_defined_of_each_parameter = Vec::new();
        for arg in fact.args_ref() {
            well_defined_of_each_parameter
                .push(self.verify_obj_well_definedness2(arg, verify_state.clone())?);
        }
        Ok(AtomicFactWellDefinedProof2 {
            well_defined_of_each_parameter,
        })
    }
}
