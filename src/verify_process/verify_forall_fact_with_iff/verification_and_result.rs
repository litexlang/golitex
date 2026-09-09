use crate::prelude::*;

pub struct VerifyForallFactWithIffResult {
    pub fact: ForallFactWithIff,
    pub well_defined_proof: ForallFactWithIffWellDefinedProof,
    pub searched_proof: ForallFactWithIffSearchedProof,
}

pub struct ForallFactWithIffSearchedProof {
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
        let searched_proof = self.search_forall_fact_with_iff_proof(fact, verify_state)?;
        Ok(VerifyForallFactWithIffResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_forall_fact_with_iff_proof(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> Result<ForallFactWithIffSearchedProof, RuntimeError> {
    }
}
