use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    PredicateSignatureWellDefinedProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyObjWellDefinedResult, ObjWellDefinedProof,
};

// Soft miss: which Obj WD failed (left or right), as Obj fail reason only.
pub struct FailToVerifyEqualFactWellDefinedResult {
    pub reason: FailToVerifyObjWellDefinedResult,
}

// Success-only evidence that both sides of an equality are well-defined.
pub struct EqualFactWellDefinedProof {
    pub left: ObjWellDefinedProof,
    pub right: ObjWellDefinedProof,
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
            predicate_signature: PredicateSignatureWellDefinedProof::Builtin,
            predicate_domain: Vec::new(),
        }
    }
}

impl From<FailToVerifyEqualFactWellDefinedResult> for FailToVerifyAtomicFactWellDefinedResult {
    fn from(fail: FailToVerifyEqualFactWellDefinedResult) -> Self {
        FailToVerifyAtomicFactWellDefinedResult::Argument(fail.reason)
    }
}
