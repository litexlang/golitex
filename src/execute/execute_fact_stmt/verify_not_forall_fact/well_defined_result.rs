use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};
use crate::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub enum FailToVerifyNotForallFactWellDefinedResult {
    ParamType {
        fact: crate::ast::fact::NotForallFact,
        reason: FailToVerifyObjWellDefinedResult,
    },
    DomFact {
        fact: crate::ast::fact::NotForallFact,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    ThenFact {
        fact: crate::ast::fact::NotForallFact,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        succeeded_then: Vec<FactWellDefinedProof>,
        failed_then: Box<FailToVerifyFactWellDefinedResult>,
    },
}

impl FailToVerifyNotForallFactWellDefinedResult {
    pub fn fact(&self) -> &crate::ast::fact::NotForallFact {
        match self {
            Self::ParamType { fact, .. }
            | Self::DomFact { fact, .. }
            | Self::ThenFact { fact, .. } => fact,
        }
    }
}

// WD for `not forall`: params → dom → then in a local binder scope.
pub enum NotForallFactWellDefinedProof {
    Compact(CompactNotForallFactWellDefinedProof),
    Normal(NormalNotForallFactWellDefinedProof),
    Detailed(Box<DetailedNotForallFactWellDefinedProof>),
}

pub struct CompactNotForallFactWellDefinedProof {}
pub struct NormalNotForallFactWellDefinedProof {}
pub struct DetailedNotForallFactWellDefinedProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub then: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

impl NotForallFactWellDefinedProof {
    pub(crate) fn new(
        detail: OutputDetail,
        build: impl FnOnce() -> DetailedNotForallFactWellDefinedProof,
    ) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactNotForallFactWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalNotForallFactWellDefinedProof {}),
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

    pub fn into_compact(self) -> RuntimeResult<CompactNotForallFactWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "quantified WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalNotForallFactWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "quantified WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_detailed(self) -> RuntimeResult<DetailedNotForallFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(*proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedNotForallFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedNotForallFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub(crate) fn detailed_ref(&self) -> &DetailedNotForallFactWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }
}

pub enum VerifyNotForallFactWellDefinedResult {
    Success(NotForallFactWellDefinedProof),
    Failed(FailToVerifyNotForallFactWellDefinedResult),
}

impl VerifyNotForallFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
