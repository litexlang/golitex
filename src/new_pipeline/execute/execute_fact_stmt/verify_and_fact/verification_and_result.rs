use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyAndFactResult2 {
    pub fact: AndFact,
    pub well_defined_proof: AndFactWellDefinedProof2,

    // Prove every conjunct in source order. Keep the child proofs on the outer
    // result so a consumer can follow the complete and-proof without a nested
    // search struct.
    pub proof_of_each_conjunct: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_and_fact2(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyAndFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_and_fact_well_definedness2(fact, verify_state.clone())?;
        let proof_of_each_conjunct = self.search_and_fact_proof2(fact, verify_state)?;
        Ok(VerifyAndFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            proof_of_each_conjunct,
        })
    }

    // Prove each conjunct as an atomic fact in source order.
    pub fn search_and_fact_proof2(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState2,
    ) -> Result<Vec<VerifyFactResult2>, RuntimeError> {
        let mut proof_of_each_conjunct = Vec::new();
        for conjunct in fact.facts.iter() {
            proof_of_each_conjunct.push(VerifyFactResult2::AtomicFact(
                self.verify_atomic_fact2(conjunct, verify_state.clone())?,
            ));
        }
        Ok(proof_of_each_conjunct)
    }
}
