use crate::prelude::*;

pub struct ForallFactWithIffWellDefinedProof {
    pub then_implies_iff: ForallFactWellDefinedProof,
    pub iff_implies_then: ForallFactWellDefinedProof,
}

impl Runtime {
    pub fn verify_forall_fact_with_iff_well_definedness(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> Result<ForallFactWithIffWellDefinedProof, RuntimeError> {
    }
}
