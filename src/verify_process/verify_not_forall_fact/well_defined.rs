use crate::prelude::*;

pub struct VerifyNotForallFactWellDefinednessResult {
    pub inner: VerifyForallFactWellDefinednessResult,
}

impl Runtime {
    pub fn verify_not_forall_fact_well_definedness(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<VerifyNotForallFactWellDefinednessResult, RuntimeError> {
    }
}
