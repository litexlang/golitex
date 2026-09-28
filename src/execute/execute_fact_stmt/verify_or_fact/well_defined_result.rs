use crate::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyFactWellDefinedResult, FactWellDefinedProof,
};

pub struct FailToVerifyOrFactWellDefinedResult {
    pub failed_index: usize,
    pub succeeded_branches: Vec<FactWellDefinedProof>,
    pub failed_branch: Box<FailToVerifyFactWellDefinedResult>,
}

// Well-definedness of an or-fact: WD each AndChainAtomic branch.
//
// Same contract as AtomicFactWellDefinedProof /
// VerifyAtomicFactWellDefinedResult: Proof is success-only;
// Result = Success(Proof) | Failed(reason).
//
// Example: `1 = 1 or 1 = 2` needs WD of both `1 = 1` and `1 = 2`.
// Example fail: `1 / 0 = 1 or 1 = 1` fails on the first branch.

// Success-only evidence that every or-branch is well-defined.
// Constructed only under Success; never embeds soft-fail.
pub struct OrFactWellDefinedProof {
    pub branches: Vec<FactWellDefinedProof>,
}

// Soft miss vs success for or-fact WD.
pub enum VerifyOrFactWellDefinedResult {
    Success(OrFactWellDefinedProof),
    Failed(FailToVerifyOrFactWellDefinedResult),
}

impl VerifyOrFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
