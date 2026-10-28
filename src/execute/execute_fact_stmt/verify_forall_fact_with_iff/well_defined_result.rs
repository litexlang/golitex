use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};
use crate::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub enum FailToVerifyForallFactWithIffWellDefinedResult {
    ParamType {
        fact: crate::ast::fact::ForallFactWithIff,
        reason: FailToVerifyObjWellDefinedResult,
    },
    DomFact {
        fact: crate::ast::fact::ForallFactWithIff,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    ThenFact {
        fact: crate::ast::fact::ForallFactWithIff,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        succeeded_then: Vec<FactWellDefinedProof>,
        failed_then: Box<FailToVerifyFactWellDefinedResult>,
    },
    IffFact {
        fact: crate::ast::fact::ForallFactWithIff,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        succeeded_then: Vec<FactWellDefinedProof>,
        succeeded_iff: Vec<FactWellDefinedProof>,
        failed_iff: Box<FailToVerifyFactWellDefinedResult>,
    },
}

impl FailToVerifyForallFactWithIffWellDefinedResult {
    pub fn fact(&self) -> &crate::ast::fact::ForallFactWithIff {
        match self {
            Self::ParamType { fact, .. }
            | Self::DomFact { fact, .. }
            | Self::ThenFact { fact, .. }
            | Self::IffFact { fact, .. } => fact,
        }
    }
}

// Surface forall-with-iff WD in one binder scope: params → dom → then → iff.
pub enum ForallFactWithIffWellDefinedProof {
    Compact(CompactForallFactWithIffWellDefinedProof),
    Normal(NormalForallFactWithIffWellDefinedProof),
    Detailed(Box<DetailedForallFactWithIffWellDefinedProof>),
}

pub struct CompactForallFactWithIffWellDefinedProof {}
pub struct NormalForallFactWithIffWellDefinedProof {}
pub struct DetailedForallFactWithIffWellDefinedProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub then: Vec<FactWellDefinedProof>,
    pub iff: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

impl ForallFactWithIffWellDefinedProof {
    pub(crate) fn new(
        detail: OutputDetail,
        build: impl FnOnce() -> DetailedForallFactWithIffWellDefinedProof,
    ) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactForallFactWithIffWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalForallFactWithIffWellDefinedProof {}),
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

    pub fn into_compact(self) -> RuntimeResult<CompactForallFactWithIffWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "quantified WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalForallFactWithIffWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "quantified WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_detailed(self) -> RuntimeResult<DetailedForallFactWithIffWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(*proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedForallFactWithIffWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(
        &mut self,
    ) -> RuntimeResult<&mut DetailedForallFactWithIffWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub(crate) fn detailed_ref(&self) -> &DetailedForallFactWithIffWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }
}

pub enum VerifyForallFactWithIffWellDefinedResult {
    Success(ForallFactWithIffWellDefinedProof),
    Failed(FailToVerifyForallFactWithIffWellDefinedResult),
}

impl VerifyForallFactWithIffWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
