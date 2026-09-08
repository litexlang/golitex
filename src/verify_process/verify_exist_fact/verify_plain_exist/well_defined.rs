use crate::prelude::*;

impl Runtime {
    pub fn verify_plain_exist_fact_well_definedness(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<VerifyExistFactWellDefinednessResult, RuntimeError> {
        self.verify_exist_fact_well_definedness(fact, verify_state)
    }
}
