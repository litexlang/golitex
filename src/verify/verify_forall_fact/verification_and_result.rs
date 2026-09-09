use crate::prelude::*;
use crate::verify_rewrite::VerifyState;

pub struct VerifyForallFactResult {
    pub fact: ForallFact,
    pub well_defined_proof: ForallFactWellDefinedProof,

    // Keep the local env so later consumers (including Lean compilation) can
    // resolve FactIds that only exist in this temporary proof scope.
    pub local_env: Environment,

    pub local_proof_results: VerifyForallFactProofLocalResults,
}

// These fields mirror the operations performed inside the temporary proof
// environment and travel together as the local part of the forall result.
pub struct VerifyForallFactProofLocalResults {
    pub local_param_def_results: LocalParamsDefResults,
    pub assumption_results: Vec<AssumptionResult>,
    pub verify_result_of_then_facts: Vec<VerifyFactResult>,
}

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
                local_param_def_results: runtime.define_forall_local_parameters(fact)?,
                assumption_results: runtime.assume_forall_domain_facts(fact, &verify_state)?,
                verify_result_of_then_facts: runtime
                    .verify_forall_then_facts(fact, &verify_state)?,
            })
        })?;
        Ok((steps, local_env))
    }

    /// Step 1 inside the temporary scope: declare forall parameters and
    /// collect the resulting parameter/type-assumption identities.
    pub fn define_forall_local_parameters(
        &mut self,
        fact: &ForallFact,
    ) -> Result<LocalParamsDefResults, RuntimeError> {
        let _ = fact;
        todo!("define forall local parameters")
    }

    /// Step 2 inside the same scope: assume each domain fact and retain the
    /// FactId and well-definedness result produced for that assumption.
    pub fn assume_forall_domain_facts(
        &mut self,
        fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<Vec<AssumptionResult>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("assume forall domain facts")
    }

    /// Step 3 inside the same scope: verify every then fact in source order,
    /// preserving each recursive verification result for downstream users.
    pub fn verify_forall_then_facts(
        &mut self,
        fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<Vec<VerifyFactResult>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("verify forall then facts")
    }
}
