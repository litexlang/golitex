use crate::new_pipeline::execute::execute_fact_stmt::verify_obj_well_defined::
    WellDefinednessProofOfObj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::prelude::*;

pub struct DraftAtomicFactWellDefinedProof {
    pub well_defined_of_each_parameter: Vec<WellDefinednessProofOfObj>,
}

impl Runtime {
    pub fn verify_draft_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<DraftAtomicFactWellDefinedProof> {
        let mut well_defined_of_each_parameter = Vec::new();
        for arg in fact.args_ref() {
            well_defined_of_each_parameter
                .push(self.verify_draft_obj_well_definedness(arg, verify_state.clone())?);
        }
        Ok(DraftAtomicFactWellDefinedProof {
            well_defined_of_each_parameter,
        })
    }
}
