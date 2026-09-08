use crate::prelude::*;

impl Runtime {
    pub fn verify_forall_fact(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<VerifyForallFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_forall_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_forall_fact_proof(fact, verify_state)?;
        Ok(VerifyForallFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_forall_fact_proof(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<ForallFactSearchedProof, RuntimeError> {
        self.execute_in_local_scope(|runtime| {})
    }
}
