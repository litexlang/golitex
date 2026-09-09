use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyForallFactResult2 {
    pub fact: ForallFact,
    pub well_defined_proof: ForallFactWellDefinedProof2,

    // Keep the local env so later consumers (including Lean compilation) can
    // resolve FactIds that only exist in this temporary proof scope.
    pub local_env: Environment,

    pub local_proof_results: VerifyForallFactProofLocalResults2,
}

// These fields mirror the operations performed inside the temporary proof
// environment and travel together as the local part of the forall result.
pub struct VerifyForallFactProofLocalResults2 {
    pub local_param_def_results: LocalParamsDefResults2,
    pub assumption_results: Vec<AssumptionResult2>,
    pub verify_result_of_then_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_forall_fact2(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyForallFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_forall_fact_well_definedness2(fact, verify_state.clone())?;
        let (local_proof_results, local_env) = self.search_forall_fact_proof2(fact, verify_state)?;
        Ok(VerifyForallFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            local_env,
            local_proof_results,
        })
    }

    /// Open the forall proof scope, run its body steps in source order, and
    /// return the child environment instead of letting the scope discard it.
    pub fn search_forall_fact_proof2(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState2,
    ) -> Result<(VerifyForallFactProofLocalResults2, Environment), RuntimeError> {
        let (steps, local_env) = self.run_in_local_env_and_take(|runtime| {
            Ok(VerifyForallFactProofLocalResults2 {
                local_param_def_results: runtime.define_forall_local_parameters2(fact)?,
                assumption_results: runtime.assume_forall_domain_facts2(fact, &verify_state)?,
                verify_result_of_then_facts: runtime
                    .verify_forall_then_facts2(fact, &verify_state)?,
            })
        })?;
        Ok((steps, local_env))
    }

    /// Step 1 inside the temporary scope: declare forall parameters and
    /// collect the resulting parameter/type-assumption identities.
    pub fn define_forall_local_parameters2(
        &mut self,
        fact: &ForallFact,
    ) -> Result<LocalParamsDefResults2, RuntimeError> {
        let _ = fact;
        todo!("define forall local parameters")
    }

    /// Step 2 inside the same scope: assume each domain fact and retain the
    /// FactId and well-definedness result produced for that assumption.
    pub fn assume_forall_domain_facts2(
        &mut self,
        fact: &ForallFact,
        verify_state: &VerifyState2,
    ) -> Result<Vec<AssumptionResult2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("assume forall domain facts")
    }

    /// Step 3 inside the same scope: verify every then fact in source order,
    /// preserving each recursive verification result for downstream users.
    pub fn verify_forall_then_facts2(
        &mut self,
        fact: &ForallFact,
        verify_state: &VerifyState2,
    ) -> Result<Vec<VerifyFactResult2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("verify forall then facts")
    }
}
