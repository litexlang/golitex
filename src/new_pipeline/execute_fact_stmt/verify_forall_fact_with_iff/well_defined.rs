use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct ForallFactWithIffWellDefinedProof2 {
    pub then_implies_iff: ForallFactWellDefinedProof2,
    pub iff_implies_then: ForallFactWellDefinedProof2,
}

impl Runtime {
    // Well-definedness of `forall ... <=>:` is well-definedness of both
    // direction forall facts from to_two_forall_facts.
    pub fn verify_forall_fact_with_iff_well_definedness2(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState2,
    ) -> Result<ForallFactWithIffWellDefinedProof2, RuntimeError> {
        let (then_implies_iff_fact, iff_implies_then_fact) = fact.to_two_forall_facts(self)?;
        let then_implies_iff = self
            .verify_forall_fact_well_definedness2(&then_implies_iff_fact, verify_state.clone())?;
        let iff_implies_then =
            self.verify_forall_fact_well_definedness2(&iff_implies_then_fact, verify_state)?;
        Ok(ForallFactWithIffWellDefinedProof2 {
            then_implies_iff,
            iff_implies_then,
        })
    }
}
