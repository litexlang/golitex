use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult, FactWellDefinedProof,
};

pub enum FailToVerifyForallFactWellDefinedResult {
    ParamType(FailToVerifyObjWellDefinedResult),
    DomFact {
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    ThenFact {
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        succeeded_then: Vec<FactWellDefinedProof>,
        failed_then: Box<FailToVerifyFactWellDefinedResult>,
    },
}

// Stage order: param types → dom facts → then facts (local binder env).
pub struct ForallFactWellDefinedProof {
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub dom: Vec<FactWellDefinedProof>,
    pub then: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

pub enum VerifyForallFactWellDefinedResult {
    Success(ForallFactWellDefinedProof),
    Failed(FailToVerifyForallFactWellDefinedResult),
}

impl VerifyForallFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
