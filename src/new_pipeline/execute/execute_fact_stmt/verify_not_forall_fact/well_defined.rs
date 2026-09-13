use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct NotForallFactWellDefinedProof {
    pub inner: ForallFactWellDefinedProof,
}

impl Runtime {
    // Well-definedness of `not forall` is well-definedness of the inner forall.
    pub fn verify_not_forall_fact_well_definedness(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<NotForallFactWellDefinedProof, RuntimeError> {
        let inner =
            self.verify_forall_fact_well_definedness(&fact.forall_fact, verify_state)?;
        Ok(NotForallFactWellDefinedProof { inner })
    }
}
