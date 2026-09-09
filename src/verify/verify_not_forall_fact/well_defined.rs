use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct NotForallFactWellDefinedProof2 {
    pub inner: ForallFactWellDefinedProof2,
}

impl Runtime {
    // Well-definedness of `not forall` is well-definedness of the inner forall.
    pub fn verify_not_forall_fact_well_definedness2(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState2,
    ) -> Result<NotForallFactWellDefinedProof2, RuntimeError> {
        let inner =
            self.verify_forall_fact_well_definedness2(&fact.forall_fact, verify_state)?;
        Ok(NotForallFactWellDefinedProof2 { inner })
    }
}
