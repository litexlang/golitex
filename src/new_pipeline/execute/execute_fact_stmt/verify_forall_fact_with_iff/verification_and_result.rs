use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct VerifyForallFactWithIffResult {
    pub fact: ForallFactWithIff,
    pub well_defined_proof: ForallFactWithIffWellDefinedProof,

    // Both directions are ordinary forall proofs. Keep them on the outer
    // result so a consumer can follow the complete iff proof without a
    // nested search enum.
    pub then_implies_iff: VerifyForallFactResult,
    pub iff_implies_then: VerifyForallFactResult,
}

impl Runtime {
    pub fn verify_forall_fact_with_iff(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> Result<VerifyForallFactWithIffResult, RuntimeError> {
        let well_defined_proof =
            self.verify_forall_fact_with_iff_well_definedness(fact, verify_state.clone())?;
        let (then_implies_iff, iff_implies_then) =
            self.search_forall_fact_with_iff_proof(fact, verify_state)?;
        Ok(VerifyForallFactWithIffResult {
            fact: fact.clone(),
            well_defined_proof,
            then_implies_iff,
            iff_implies_then,
        })
    }

    // Split `forall ... <=>:` into two forall facts and verify each direction:
    // 1. `dom + then` proves `iff`.
    // 2. `dom + iff` proves `then`.
    pub fn search_forall_fact_with_iff_proof(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> Result<(VerifyForallFactResult, VerifyForallFactResult), RuntimeError> {
        let (then_implies_iff_fact, iff_implies_then_fact) = fact.to_two_forall_facts(self)?;
        let then_implies_iff =
            self.verify_forall_fact(&then_implies_iff_fact, verify_state.clone())?;
        let iff_implies_then = self.verify_forall_fact(&iff_implies_then_fact, verify_state)?;
        Ok((then_implies_iff, iff_implies_then))
    }
}
