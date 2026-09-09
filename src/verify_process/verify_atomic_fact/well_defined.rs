use crate::prelude::*;

pub struct AtomicFactWellDefinedProof {
    pub well_defined_of_each_parameter: Vec<WellDefinednessProofOfObj>,
}

impl Runtime {
    pub fn verify_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> Result<AtomicFactWellDefinedProof, RuntimeError> {
        let mut well_defined_of_each_parameter = Vec::new();
        for arg in fact.args_ref() {
            well_defined_of_each_parameter
                .push(self.verify_obj_well_definedness(arg, verify_state.clone())?);
        }
        Ok(AtomicFactWellDefinedProof {
            well_defined_of_each_parameter,
        })
    }
}
