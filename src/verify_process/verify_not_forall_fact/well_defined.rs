use crate::prelude::*;

pub struct NotForallFactWellDefinedProof {
    pub inner: ForallFactWellDefinedProof,
}

impl Runtime {
    pub fn verify_not_forall_fact_well_definedness(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<NotForallFactWellDefinedProof, RuntimeError> {
    }
}
