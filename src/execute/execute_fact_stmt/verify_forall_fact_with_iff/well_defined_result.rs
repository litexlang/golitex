use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};
use crate::execute::introduce_typed_parameters::IntroduceTypedParametersResult;

pub enum FailToVerifyForallFactWithIffWellDefinedResult {
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
    IffFact {
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        succeeded_then: Vec<FactWellDefinedProof>,
        succeeded_iff: Vec<FactWellDefinedProof>,
        failed_iff: Box<FailToVerifyFactWellDefinedResult>,
    },
}

// Surface forall-with-iff WD in one binder scope: params → dom → then → iff.
pub struct ForallFactWithIffWellDefinedProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub then: Vec<FactWellDefinedProof>,
    pub iff: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

pub enum VerifyForallFactWithIffWellDefinedResult {
    Success(ForallFactWithIffWellDefinedProof),
    Failed(FailToVerifyForallFactWithIffWellDefinedResult),
}

impl VerifyForallFactWithIffWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
