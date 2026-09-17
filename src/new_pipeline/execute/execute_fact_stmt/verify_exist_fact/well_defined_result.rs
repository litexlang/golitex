use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};

pub enum FailToVerifyExistFactWellDefinedResult {
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
// 1. param-type WD
// 2. define binders so body can treat them as known
// 3. WD each QuantifierFree body clause
// 4. keep that local_env as proof evidence (same idea as forall / or selected-branch)
//
// Example: `exist x R st {x = 1}` needs `R` WD, then binder `x`, then WD of `x = 1`.

// Success-only evidence (same contract as AtomicFactWellDefinedProof).
// Constructed only under Success; never embeds soft-fail.
// Field order = stage order; `local_env` is the closed binder scope (not merged).
pub struct ExistFactWellDefinedProof {
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub body: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

// Soft miss vs success for exist-fact WD. Same shape as
// VerifyAtomicFactWellDefinedResult: Success(Proof) | Failed(reason).
// Proof never embeds Fail.
pub enum VerifyExistFactWellDefinedResult {
    Success(ExistFactWellDefinedProof),
    Failed(FailToVerifyExistFactWellDefinedResult),
}

impl VerifyExistFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
