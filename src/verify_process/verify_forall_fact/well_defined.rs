use crate::prelude::*;

pub struct ForallFactWellDefinedProof {
    pub param_def_results: LocalParameterDefinitionResult,
    pub domain_assumptions: Vec<AssumptionResult>,

    pub local_env: Environment,

    pub well_defined_proof_of_then_facts: Vec<FactWellDefinedProof>,
}

impl Runtime {
    pub fn verify_forall_fact_well_definedness(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<ForallFactWellDefinedProof, RuntimeError> {
        Ok(ForallFactWellDefinedProof {})
    }
}
