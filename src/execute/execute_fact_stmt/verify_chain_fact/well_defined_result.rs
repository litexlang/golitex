use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};

pub struct FailToVerifyChainFactWellDefinedResult {
    pub failed_index: usize,
    pub succeeded_adjacent: Vec<AtomicFactWellDefinedProof>,
    pub failed_adjacent: FailToVerifyAtomicFactWellDefinedResult,
}

// Success-only evidence that every adjacent chain atomic is well-defined.
// Example: `1 < 2 < 3` needs WD of `1 < 2` and `2 < 3`.
pub struct ChainFactWellDefinedProof {
    pub adjacent: Vec<AtomicFactWellDefinedProof>,
}

// Soft miss vs success for chain-fact WD.
pub enum VerifyChainFactWellDefinedResult {
    Success(ChainFactWellDefinedProof),
    Failed(FailToVerifyChainFactWellDefinedResult),
}

impl VerifyChainFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
