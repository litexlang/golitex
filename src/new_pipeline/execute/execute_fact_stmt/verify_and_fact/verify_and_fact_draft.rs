use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

use super::verify_and_fact_result::VerifyAndFactResult;

impl Runtime {
    pub fn verify_and_fact(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> Result<VerifyAndFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_and_fact_well_definedness(fact, verify_state.clone())?;
        let proof_of_each_conjunct = self.search_and_fact_proof(fact, verify_state)?;
        Ok(VerifyAndFactResult {
            fact: fact.clone(),
            well_defined_proof,
            proof_of_each_conjunct,
        })
    }

    // Prove each conjunct as an atomic fact in source order.
    pub fn search_and_fact_proof(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> Result<Vec<VerifyFactResult>, RuntimeError> {
        let mut proof_of_each_conjunct = Vec::new();
        for conjunct in fact.facts.iter() {
            let proof = self.verify_atomic_fact(conjunct, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(vec![proof]);
            }
            proof_of_each_conjunct.push(proof);
        }
        Ok(proof_of_each_conjunct)
    }
}
