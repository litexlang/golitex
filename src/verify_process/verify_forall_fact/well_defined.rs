use crate::prelude::*;

pub struct ForallFactWellDefinedProof {
    pub local_env: Environment,

    pub local_proof_results: ForallFactWellDefinedProofLocalResults,
}

pub struct ForallFactWellDefinedProofLocalResults {
    pub param_def_results: LocalParamsDefResults,
    pub domain_assumptions: Vec<AssumptionResult>,
    pub well_defined_proof_of_then_facts: Vec<FactWellDefinedProof>,
}

impl Runtime {
    // Open a temporary forall scope, declare parameters, assume domain facts,
    // then check well-definedness of each then-fact inside that scope.
    pub fn verify_forall_fact_well_definedness(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<ForallFactWellDefinedProof, RuntimeError> {
        let (local_proof_results, local_env) = self.run_in_local_env_and_take(|runtime| {
            let param_def_results = runtime.local_params_define(fact.typed_parameters.clone())?;
            let domain_assumptions = runtime.local_assume(fact.dom_facts.clone())?;
            let mut well_defined_proof_of_then_facts = Vec::new();
            for then_fact in fact.then_facts.iter() {
                well_defined_proof_of_then_facts.push(runtime.verify_fact_well_definedness(
                    &then_fact.clone().to_fact(),
                    verify_state.clone(),
                )?);
            }
            Ok(ForallFactWellDefinedProofLocalResults {
                param_def_results,
                domain_assumptions,
                well_defined_proof_of_then_facts,
            })
        })?;

        Ok(ForallFactWellDefinedProof {
            local_env,
            local_proof_results,
        })
    }
}
