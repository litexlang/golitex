use crate::new_pipeline::execute::execute_fact_stmt::verify_and_fact::FailToVerifyAndFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_chain_fact::FailToVerifyChainFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::{
    ExistFactWellDefinedProof, FailToVerifyExistFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::{
    FailToVerifyForallFactWellDefinedResult, ForallFactWellDefinedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact_with_iff::{
    FailToVerifyForallFactWithIffWellDefinedResult, ForallFactWithIffWellDefinedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_not_forall_fact::{
    FailToVerifyNotForallFactWellDefinedResult, NotForallFactWellDefinedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof,
};

pub enum FailToVerifyFactWellDefinedResult {
    Equality(FailToVerifyAtomicFactWellDefinedResult),
    AtomicExceptEquality(FailToVerifyAtomicFactWellDefinedResult),
    AndFact(FailToVerifyAndFactWellDefinedResult),
    ChainFact(FailToVerifyChainFactWellDefinedResult),
    OrFact(FailToVerifyOrFactWellDefinedResult),
    ExistFact(FailToVerifyExistFactWellDefinedResult),
    ForallFact(FailToVerifyForallFactWellDefinedResult),
    ForallFactWithIff(FailToVerifyForallFactWithIffWellDefinedResult),
    NotForall(FailToVerifyNotForallFactWellDefinedResult),
}

// Success-only evidence that a Fact is well-defined.
pub enum FactWellDefinedProof {
    AtomicFact(AtomicFactWellDefinedProof),
    AndFact {
        components: Vec<AtomicFactWellDefinedProof>,
    },
    ChainFact {
        adjacent: Vec<AtomicFactWellDefinedProof>,
    },
    OrFact(OrFactWellDefinedProof),
    ExistFact(ExistFactWellDefinedProof),
    ForallFact(ForallFactWellDefinedProof),
    ForallFactWithIff(ForallFactWithIffWellDefinedProof),
    NotForall(NotForallFactWellDefinedProof),
}

// Soft miss vs success for fact WD. Proof never embeds Fail.
pub enum VerifyFactWellDefinedResult {
    Success(FactWellDefinedProof),
    Failed(FailToVerifyFactWellDefinedResult),
}

impl VerifyFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
