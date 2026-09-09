use crate::prelude::*;

pub struct ExistFactWellDefinedProof {
    pub local_param_def_results: LocalParamsDefResults,
    pub local_env: Environment,
    pub proof_of_well_definedness_of_facts_inside: Vec<FactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_exist_fact_well_definedness(
        &mut self,
        fact: &ExistentialSpec,
        verify_state: VerifyState,
    ) -> Result<ExistFactWellDefinedProof, RuntimeError> {
        Ok(ExistFactWellDefinedProof {})
    }
}
