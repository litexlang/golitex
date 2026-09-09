use crate::prelude::*;

pub struct ExistFactWellDefinedProof {
    pub local_param_def_results: LocalParameterDefinitionResult,
    pub local_env: Environment,
    pub proof_of_facts_inside_exist_Fact: Vec<FactWellDefinedProof>,
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
