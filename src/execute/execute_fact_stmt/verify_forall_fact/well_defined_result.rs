use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};

pub enum FailToVerifyForallFactWellDefinedResult {
    ParamType(FailToVerifyObjWellDefinedResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
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

// Stage order: param types/bindings → one struct layer → dom facts → then facts.
pub struct ForallFactWellDefinedProof {
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub auto_opened_struct_layers:
        Option<Vec<crate::execute::release_one_struct_layer::ReleaseOneStructLayerProof>>,
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
