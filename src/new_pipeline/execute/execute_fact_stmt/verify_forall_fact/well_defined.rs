use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct ForallFactWellDefinedProof2 {
    pub local_env: Environment,

    pub local_proof_results: ForallFactWellDefinedProofLocalResults2,
}

pub struct ForallFactWellDefinedProofLocalResults2 {
    pub param_def_results: LocalParamsDefResults2,
    pub domain_assumptions: Vec<AssumptionResult2>,
    pub well_defined_proof_of_then_facts: Vec<FactWellDefinedProof2>,
}

impl Runtime {
    // Open a temporary forall scope, declare parameters, assume domain facts,
    // then check well-definedness of each then-fact inside that scope.
    pub fn verify_forall_fact_well_definedness2(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState2,
    ) -> Result<ForallFactWellDefinedProof2, RuntimeError> {
        let (local_proof_results, local_env) = self.run_in_local_env_and_take(|runtime| {
            let param_def_results = runtime.local_params_define2(fact.typed_parameters.clone())?;
            let domain_assumptions = runtime.local_assume2(fact.dom_facts.clone())?;
            let mut well_defined_proof_of_then_facts = Vec::new();
            for then_fact in fact.then_facts.iter() {
                well_defined_proof_of_then_facts.push(runtime.verify_fact_well_definedness2(
                    &then_fact.clone().to_fact(),
                    verify_state.clone(),
                )?);
            }
            Ok(ForallFactWellDefinedProofLocalResults2 {
                param_def_results,
                domain_assumptions,
                well_defined_proof_of_then_facts,
            })
        })?;

        Ok(ForallFactWellDefinedProof2 {
            local_env,
            local_proof_results,
        })
    }
}
