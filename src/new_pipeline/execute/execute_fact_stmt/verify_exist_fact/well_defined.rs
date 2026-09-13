use crate::fact::PlainExistFact;
use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct ExistFactWellDefinedProof {
    pub local_env: Environment,

    pub local_proof_results: ExistFactWellDefinedProofLocalResults,
}

pub struct ExistFactWellDefinedProofLocalResults {
    pub local_param_def_results: LocalParamsDefResults,
    pub proof_of_well_definedness_of_facts_inside: Vec<DraftFactWellDefinedProof>,
}

impl Runtime {
    // Open a temporary binder scope, declare exist parameters, then check
    // well-definedness of each body fact inside that scope.
    pub fn verify_exist_fact_well_definedness(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<ExistFactWellDefinedProof, RuntimeError> {
        let (local_proof_results, local_env) = self.run_in_local_env_and_take(|runtime| {
            let local_param_def_results =
                runtime.local_params_define(fact.typed_parameters.clone())?;
            let mut proof_of_well_definedness_of_facts_inside = Vec::new();
            for body_fact in fact.facts.iter() {
                proof_of_well_definedness_of_facts_inside.push(
                    runtime.verify_draft_fact_well_definedness(
                        &body_fact.clone().into(),
                        verify_state.clone(),
                    )?,
                );
            }
            Ok(ExistFactWellDefinedProofLocalResults {
                local_param_def_results,
                proof_of_well_definedness_of_facts_inside,
            })
        })?;

        Ok(ExistFactWellDefinedProof {
            local_env,
            local_proof_results,
        })
    }
}
