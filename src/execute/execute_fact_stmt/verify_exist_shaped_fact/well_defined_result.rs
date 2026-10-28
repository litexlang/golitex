use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};
use crate::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub enum FailToVerifyExistShapedFactWellDefinedResult {
    ParamType {
        fact: crate::ast::fact::ExistShapedFact,
        reason: FailToVerifyObjWellDefinedResult,
    },
    BodyFact {
        fact: crate::ast::fact::ExistShapedFact,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_body: Vec<FactWellDefinedProof>,
        failed_body: Box<FailToVerifyFactWellDefinedResult>,
    },
}

impl FailToVerifyExistShapedFactWellDefinedResult {
    pub fn fact(&self) -> &crate::ast::fact::ExistShapedFact {
        match self {
            Self::ParamType { fact, .. } | Self::BodyFact { fact, .. } => fact,
        }
    }
}

// Well-definedness of an exist / exist! / not-exist fact.
//
// Local binder scope (not merged into the parent):
// 1. introduce params (type WD + define binders)
// 2. WD each QuantifierFree body clause and assume it for later clauses
// 3. keep that local_env as proof evidence (same idea as forall / or selected-branch)
//
// Example: `exist x R st {x = 1}` needs `R` WD, then binder `x`, then WD of `x = 1`.

// Success-only evidence (same contract as AtomicFactWellDefinedProof).
// Constructed only under Success; never embeds soft-fail.
// Field order = stage order; `local_env` is the closed binder scope (not merged).
pub enum ExistShapedFactWellDefinedProof {
    Compact(CompactExistShapedFactWellDefinedProof),
    Normal(NormalExistShapedFactWellDefinedProof),
    Detailed(Box<DetailedExistShapedFactWellDefinedProof>),
}

pub struct CompactExistShapedFactWellDefinedProof {}
pub struct NormalExistShapedFactWellDefinedProof {}
pub struct DetailedExistShapedFactWellDefinedProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_body_facts: Vec<AssumeDomFactResult>,
    pub local_env: Box<ExecEnv>,
}

impl ExistShapedFactWellDefinedProof {
    pub(crate) fn new(
        detail: OutputDetail,
        build: impl FnOnce() -> DetailedExistShapedFactWellDefinedProof,
    ) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactExistShapedFactWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalExistShapedFactWellDefinedProof {}),
            OutputDetail::Detailed => Self::Detailed(Box::new(build())),
        }
    }

    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }

    pub fn into_compact(self) -> RuntimeResult<CompactExistShapedFactWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "quantified WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalExistShapedFactWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "quantified WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_detailed(self) -> RuntimeResult<DetailedExistShapedFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(*proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedExistShapedFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(
        &mut self,
    ) -> RuntimeResult<&mut DetailedExistShapedFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub(crate) fn detailed_ref(&self) -> &DetailedExistShapedFactWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }
}

// Soft miss vs success for exist-fact WD. Same shape as
// VerifyAtomicFactWellDefinedResult: Success(Proof) | Failed(reason).
// Proof never embeds Fail.
pub enum VerifyExistShapedFactWellDefinedResult {
    Success(ExistShapedFactWellDefinedProof),
    Failed(FailToVerifyExistShapedFactWellDefinedResult),
}

impl VerifyExistShapedFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
