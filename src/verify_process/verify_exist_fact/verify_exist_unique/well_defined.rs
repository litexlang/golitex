use crate::prelude::*;

pub struct ExistUniqueFactWellDefinedProof {
    pub well_defined_of_each_body_fact: Vec<QuantifierFreeFactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_exist_unique_fact_well_definedness(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<ExistUniqueFactWellDefinedProof, RuntimeError> {
        let well_defined_of_each_body_fact =
            self.verify_existential_spec_body_well_definedness(fact, verify_state)?;
        Ok(ExistUniqueFactWellDefinedProof {
            well_defined_of_each_body_fact,
        })
    }
}
