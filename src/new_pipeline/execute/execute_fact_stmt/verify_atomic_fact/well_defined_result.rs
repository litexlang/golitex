use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyObjWellDefinedResult, VerifyObjWellDefinedResult,
};

pub struct FailToVerifyAtomicFactWellDefinedResult {
    pub failed_arg_index: usize,
    pub succeeded_args: Vec<VerifyObjWellDefinedResult>,
    pub reason: FailToVerifyObjWellDefinedResult,
}

// Success-only evidence that every argument of an atomic fact is well-defined.
pub struct AtomicFactWellDefinedProof {
    // Constructed only under Success; each entry is ByKnown or ByDef.
    pub well_defined_of_each_parameter: Vec<VerifyObjWellDefinedResult>,
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
