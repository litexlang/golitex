use crate::prelude::*;

pub struct VerifyForallFactResult {
    pub fact: ForallFact,
    pub well_defined_proof: ForallFactWellDefinedProof,

    pub local_param_def_results: LocalParamsDefResults,
    pub assumption_results: Vec<AssumptionResult>,

    pub local_env: Environment, // Keep the local env so searched_proof can cite facts that only exist there.
    pub verify_result_of_then_facts: Vec<VerifyFactResult>,
}

pub struct ForallFactSearchedProof {
    pub proof_of_each_then_fact: Vec<VerifyFactResult>,
}

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
        // This search must produce the local env and store it on the result.
        let local_env = self.execute_in_local_scope(|runtime| {});
    }
}
