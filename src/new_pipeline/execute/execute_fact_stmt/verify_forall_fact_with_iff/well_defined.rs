use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct ForallFactWithIffWellDefinedProof {
    pub then_implies_iff: ForallFactWellDefinedProof,
    pub iff_implies_then: ForallFactWellDefinedProof,
}

impl Runtime {
    // Well-definedness of `forall ... <=>:` is well-definedness of both
    // direction forall facts from to_two_forall_facts.
    pub fn verify_forall_fact_with_iff_well_definedness(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> Result<ForallFactWithIffWellDefinedProof, RuntimeError> {
        let (then_implies_iff_fact, iff_implies_then_fact) = fact.to_two_forall_facts(self)?;
        let then_implies_iff = self
            .verify_forall_fact_well_definedness(&then_implies_iff_fact, verify_state.clone())?;
        let iff_implies_then =
            self.verify_forall_fact_well_definedness(&iff_implies_then_fact, verify_state)?;
        Ok(ForallFactWithIffWellDefinedProof {
            then_implies_iff,
            iff_implies_then,
        })
    }
}
