use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};
use crate::execute::introduce_typed_parameters::IntroduceTypedParametersResult;

pub enum FailToVerifyExistShapedFactWellDefinedResult {
    ParamType(FailToVerifyObjWellDefinedResult),
    BodyFact {
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_body: Vec<FactWellDefinedProof>,
        failed_body: Box<FailToVerifyFactWellDefinedResult>,
    },
}

// Well-definedness of an exist / exist! / not-exist fact.
//
// Local binder scope (not merged into the parent):
// 1. introduce params (type WD + define binders)
// 2. WD each QuantifierFree body clause and assume it for later clauses
// 3. keep that local_env as proof evidence (same idea as forall / or selected-branch)
//
// Example: `exist x R st {x = 1}` needs `R` WD, then binder `x`, then WD of `x = 1`.

// Success-only evidence (same contract as AtomicFactWellDefinedProof).
// Constructed only under Success; never embeds soft-fail.
// Field order = stage order; `local_env` is the closed binder scope (not merged).
pub struct ExistShapedFactWellDefinedProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_body_facts: Vec<AssumeDomFactResult>,
    pub local_env: Box<ExecEnv>,
}

// Soft miss vs success for exist-fact WD. Same shape as
// VerifyAtomicFactWellDefinedResult: Success(Proof) | Failed(reason).
// Proof never embeds Fail.
pub enum VerifyExistShapedFactWellDefinedResult {
    Success(ExistShapedFactWellDefinedProof),
    Failed(FailToVerifyExistShapedFactWellDefinedResult),
}

impl VerifyExistShapedFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
