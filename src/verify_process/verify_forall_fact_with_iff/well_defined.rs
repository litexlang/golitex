use crate::prelude::*;

pub struct VerifyForallFactWithIffWellDefinednessResult {
    pub then_implies_iff: VerifyForallFactWellDefinednessResult,
    pub iff_implies_then: VerifyForallFactWellDefinednessResult,
}

impl Runtime {
    pub fn verify_forall_fact_with_iff_well_definedness(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> Result<VerifyForallFactWithIffWellDefinednessResult, RuntimeError> {
    }
}
