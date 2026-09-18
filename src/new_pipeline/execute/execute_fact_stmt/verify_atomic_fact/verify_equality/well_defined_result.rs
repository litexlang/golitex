use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyObjWellDefinedResult, VerifyObjWellDefinedResult,
};

// Soft miss while checking left/right of an EqualFact.
// Index 0 = left, 1 = right.
pub struct FailToVerifyEqualFactWellDefinedResult {
    pub failed_arg_index: usize,
    pub succeeded_args: Vec<VerifyObjWellDefinedResult>,
    pub reason: FailToVerifyObjWellDefinedResult,
}

// Success-only evidence that both sides of an equality are well-defined.
pub struct EqualFactWellDefinedProof {
    pub left: VerifyObjWellDefinedResult,
    pub right: VerifyObjWellDefinedResult,
}

pub enum VerifyEqualFactWellDefinedResult {
    Success(EqualFactWellDefinedProof),
    Failed(FailToVerifyEqualFactWellDefinedResult),
}

impl VerifyEqualFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// And/chain still store mixed atomics as AtomicFactWellDefinedProof.
impl From<EqualFactWellDefinedProof> for AtomicFactWellDefinedProof {
    fn from(proof: EqualFactWellDefinedProof) -> Self {
        AtomicFactWellDefinedProof {
            well_defined_of_each_parameter: vec![proof.left, proof.right],
        }
    }
}

impl From<FailToVerifyEqualFactWellDefinedResult> for FailToVerifyAtomicFactWellDefinedResult {
    fn from(fail: FailToVerifyEqualFactWellDefinedResult) -> Self {
        FailToVerifyAtomicFactWellDefinedResult {
            failed_arg_index: fail.failed_arg_index,
            succeeded_args: fail.succeeded_args,
            reason: fail.reason,
        }
    }
}
