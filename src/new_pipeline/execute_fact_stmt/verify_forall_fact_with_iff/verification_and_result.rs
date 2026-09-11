use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyForallFactWithIffResult2 {
    pub fact: ForallFactWithIff,
    pub well_defined_proof: ForallFactWithIffWellDefinedProof2,

    // Both directions are ordinary forall proofs. Keep them on the outer
    // result so a consumer can follow the complete iff proof without a
    // nested search enum.
    pub then_implies_iff: VerifyForallFactResult2,
    pub iff_implies_then: VerifyForallFactResult2,
}

impl Runtime {
    pub fn verify_forall_fact_with_iff2(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState2,
    ) -> Result<VerifyForallFactWithIffResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_forall_fact_with_iff_well_definedness2(fact, verify_state.clone())?;
        let (then_implies_iff, iff_implies_then) =
            self.search_forall_fact_with_iff_proof2(fact, verify_state)?;
        Ok(VerifyForallFactWithIffResult2 {
            fact: fact.clone(),
            well_defined_proof,
            then_implies_iff,
            iff_implies_then,
        })
    }

    // Split `forall ... <=>:` into two forall facts and verify each direction:
    // 1. `dom + then` proves `iff`.
    // 2. `dom + iff` proves `then`.
    pub fn search_forall_fact_with_iff_proof2(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState2,
    ) -> Result<(VerifyForallFactResult2, VerifyForallFactResult2), RuntimeError> {
        let (then_implies_iff_fact, iff_implies_then_fact) = fact.to_two_forall_facts(self)?;
        let then_implies_iff =
            self.verify_forall_fact2(&then_implies_iff_fact, verify_state.clone())?;
        let iff_implies_then = self.verify_forall_fact2(&iff_implies_then_fact, verify_state)?;
        Ok((then_implies_iff, iff_implies_then))
    }
}
