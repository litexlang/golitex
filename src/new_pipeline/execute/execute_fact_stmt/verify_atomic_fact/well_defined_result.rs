use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyObjWellDefinedResult, ObjWellDefinedProof,
};

// Soft miss: the first argument Obj WD that failed, and why.
pub struct FailToVerifyAtomicFactWellDefinedResult {
    pub reason: FailToVerifyObjWellDefinedResult,
}

// Success-only evidence that every argument of an atomic fact is well-defined.
pub struct AtomicFactWellDefinedProof {
    pub well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
}

// Soft miss vs success for atomic-fact WD. Proof never embeds Fail.
pub enum VerifyAtomicFactWellDefinedResult {
    Success(AtomicFactWellDefinedProof),
    Failed(FailToVerifyAtomicFactWellDefinedResult),
}

impl VerifyAtomicFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
