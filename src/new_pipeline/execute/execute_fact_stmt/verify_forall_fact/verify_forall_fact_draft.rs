use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

use super::verify_forall_fact_result::{
    VerifyForallFactResult,
    VerifyForallFactProofLocalResults,
};

impl Runtime {
    pub fn verify_forall_fact(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<VerifyForallFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_forall_fact_well_definedness(fact, verify_state.clone())?;
        let (local_proof_results, local_env) = self.search_forall_fact_proof(fact, verify_state)?;
        Ok(VerifyForallFactResult {
            fact: fact.clone(),
            well_defined_proof,
            local_env,
            local_proof_results,
        })
    }

    /// Open the forall proof scope, run its body steps in source order, and
    /// return the child environment instead of letting the scope discard it.
    pub fn search_forall_fact_proof(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<(VerifyForallFactProofLocalResults, Environment), RuntimeError> {
        let (steps, local_env) = self.run_in_local_env_and_take(|runtime| {
            Ok(VerifyForallFactProofLocalResults {
                local_param_def_results: runtime
                    .local_params_define(fact.typed_parameters.clone())?,
                assumption_results: runtime.local_assume(fact.dom_facts.clone())?,
                verify_result_of_then_facts: runtime
                    .verify_forall_then_facts(fact, &verify_state)?,
            })
        })?;
        Ok((steps, local_env))
    }

    // Inside the temporary scope: verify every then fact in source order.
    pub fn verify_forall_then_facts(
        &mut self,
        fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<Vec<VerifyFactResult>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("verify forall then facts")
    }
}
