use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};

pub enum FailToVerifyNotForallFactWellDefinedResult {
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

// WD for `not forall`: params → dom → then in a local binder scope.
pub struct NotForallFactWellDefinedProof {
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub dom: Vec<FactWellDefinedProof>,
    pub then: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

pub enum VerifyNotForallFactWellDefinedResult {
    Success(NotForallFactWellDefinedProof),
    Failed(FailToVerifyNotForallFactWellDefinedResult),
}

impl VerifyNotForallFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
