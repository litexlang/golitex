use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};

pub struct FailToVerifyAndFactWellDefinedResult {
    pub failed_index: usize,
    pub succeeded_components: Vec<AtomicFactWellDefinedProof>,
    pub failed_component: FailToVerifyAtomicFactWellDefinedResult,
}

// Success-only evidence that every and-conjunct is well-defined.
// Example: `1 < 2 and 2 < 3` needs WD of both atomics.
pub struct AndFactWellDefinedProof {
    pub components: Vec<AtomicFactWellDefinedProof>,
}

// Soft miss vs success for and-fact WD.
pub enum VerifyAndFactWellDefinedResult {
    Success(AndFactWellDefinedProof),
    Failed(FailToVerifyAndFactWellDefinedResult),
}

impl VerifyAndFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
