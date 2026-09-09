use crate::prelude::*;

pub struct VerifyAndFactResult {
    pub fact: AndFact,
    pub well_defined_proof: AndFactWellDefinedProof,

    // Prove every conjunct in source order. Keep the child proofs on the outer
    // result so a consumer can follow the complete and-proof without a nested
    // search struct.
    pub proof_of_each_conjunct: Vec<VerifyFactResult>,
}

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
            proof_of_each_conjunct.push(VerifyFactResult::AtomicFact(
                self.verify_atomic_fact(conjunct, verify_state.clone())?,
            ));
        }
        Ok(proof_of_each_conjunct)
    }
}
