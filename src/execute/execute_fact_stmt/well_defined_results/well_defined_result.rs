use crate::execute::execute_fact_stmt::verify_and_fact::{
    AndFactWellDefinedProof, FailToVerifyAndFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualFactWellDefinedProof, FailToVerifyEqualFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_chain_fact::{
    ChainFactWellDefinedProof, FailToVerifyChainFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactWellDefinedProof, FailToVerifyExistShapedFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    FailToVerifyForallFactWellDefinedResult, ForallFactWellDefinedProof,
};
use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::{
    FailToVerifyForallFactWithIffWellDefinedResult, ForallFactWithIffWellDefinedProof,
};
use crate::execute::execute_fact_stmt::verify_not_forall_fact::{
    FailToVerifyNotForallFactWellDefinedResult, NotForallFactWellDefinedProof,
};
use crate::execute::execute_fact_stmt::verify_or_fact::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof,
};

pub enum FailToVerifyFactWellDefinedResult {
    Equality(FailToVerifyEqualFactWellDefinedResult),
    AtomicExceptEquality(FailToVerifyAtomicFactWellDefinedResult),
    AndFact(FailToVerifyAndFactWellDefinedResult),
    ChainFact(FailToVerifyChainFactWellDefinedResult),
    OrFact(FailToVerifyOrFactWellDefinedResult),
    ExistFact(FailToVerifyExistShapedFactWellDefinedResult),
    ForallFact(FailToVerifyForallFactWellDefinedResult),
    ForallFactWithIff(FailToVerifyForallFactWithIffWellDefinedResult),
    NotForall(FailToVerifyNotForallFactWellDefinedResult),
}

impl FailToVerifyFactWellDefinedResult {
    pub fn fact(&self) -> crate::ast::fact::Fact {
        use crate::ast::fact::Fact;
        match self {
            Self::Equality(failed) => failed.fact.clone().into(),
            Self::AtomicExceptEquality(failed) => failed.fact().clone().into(),
            Self::AndFact(failed) => Fact::AndFact(failed.fact.clone()),
            Self::ChainFact(failed) => Fact::ChainFact(failed.fact.clone()),
            Self::OrFact(failed) => Fact::OrFact(failed.fact.clone()),
            Self::ExistFact(failed) => crate::ast::fact::exist_shaped_fact_to_fact(failed.fact()),
            Self::ForallFact(failed) => Fact::ForallFact(failed.fact().clone()),
            Self::ForallFactWithIff(failed) => Fact::ForallFactWithIff(failed.fact().clone()),
            Self::NotForall(failed) => Fact::NotForall(failed.fact().clone()),
        }
    }
}

// Success-only evidence that a Fact is well-defined.
pub enum FactWellDefinedProof {
    Equality(EqualFactWellDefinedProof),
    AtomicExceptEquality(AtomicFactWellDefinedProof),
    AndFact(AndFactWellDefinedProof),
    ChainFact(ChainFactWellDefinedProof),
    OrFact(OrFactWellDefinedProof),
    ExistFact(ExistShapedFactWellDefinedProof),
    ForallFact(ForallFactWellDefinedProof),
    ForallFactWithIff(ForallFactWithIffWellDefinedProof),
    NotForall(NotForallFactWellDefinedProof),
}

impl FactWellDefinedProof {
    pub fn detail(&self) -> crate::result_detail::OutputDetail {
        match self {
            Self::Equality(proof) => proof.detail(),
            Self::AtomicExceptEquality(proof) => proof.detail(),
            Self::AndFact(proof) => proof.detail(),
            Self::ChainFact(proof) => proof.detail(),
            Self::OrFact(proof) => proof.detail(),
            Self::ExistFact(proof) => proof.detail(),
            Self::ForallFact(proof) => proof.detail(),
            Self::ForallFactWithIff(proof) => proof.detail(),
            Self::NotForall(proof) => proof.detail(),
        }
    }

    pub fn require_detail(
        &self,
        expected: crate::result_detail::OutputDetail,
        stage: &str,
    ) -> crate::runtime::RuntimeResult<()> {
        expected.require(self.detail(), stage)
    }
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
