use crate::fact::PlainExistFact;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct ExistFactWellDefinedProof2 {
    pub local_env: Environment,

    pub local_proof_results: ExistFactWellDefinedProofLocalResults2,
}

pub struct ExistFactWellDefinedProofLocalResults2 {
    pub local_param_def_results: LocalParamsDefResults2,
    pub proof_of_well_definedness_of_facts_inside: Vec<FactWellDefinedProof2>,
}

impl Runtime {
    // Open a temporary binder scope, declare exist parameters, then check
    // well-definedness of each body fact inside that scope.
    pub fn verify_exist_fact_well_definedness2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<ExistFactWellDefinedProof2, RuntimeError> {
        let (local_proof_results, local_env) = self.run_in_local_env_and_take(|runtime| {
            let local_param_def_results =
                runtime.local_params_define2(fact.typed_parameters.clone())?;
            let mut proof_of_well_definedness_of_facts_inside = Vec::new();
            for body_fact in fact.facts.iter() {
                proof_of_well_definedness_of_facts_inside.push(
                    runtime.verify_fact_well_definedness2(
                        &body_fact.clone().into(),
                        verify_state.clone(),
                    )?,
                );
            }
            Ok(ExistFactWellDefinedProofLocalResults2 {
                local_param_def_results,
                proof_of_well_definedness_of_facts_inside,
            })
        })?;

        Ok(ExistFactWellDefinedProof2 {
            local_env,
            local_proof_results,
        })
    }
}
