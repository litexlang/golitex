use crate::new_pipeline::execute::execute_fact_stmt::verify_obj_well_defined::
    WellDefinednessProofOfObj2;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::prelude::*;

pub struct AtomicFactWellDefinedProof2 {
    pub well_defined_of_each_parameter: Vec<WellDefinednessProofOfObj2>,
}

impl Runtime {
    pub fn verify_atomic_fact_well_definedness2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<AtomicFactWellDefinedProof2> {
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
