use super::result::AssumeDomFactResult;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::VerifyAndDefineWdParametersFailed;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult,
};
use crate::execute::IntroduceTypedParametersFailed;
use crate::execute::IntroduceTypedParametersResult;
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub enum FailToVerifyForallFactWellDefinedResult {
    LocalIntroduction(Box<ForallIntroductionFormationFailure>),
    LocalWellDefinedness(Box<ForallWellDefinedLocalFailure>),
    ParamType {
        fact: crate::ast::fact::ForallFact,
        reason: FailToVerifyObjWellDefinedResult,
    },
    AutoOpenStructLayer {
        fact: crate::ast::fact::ForallFact,
        reason: crate::execute::FailToReleaseOneStructLayer,
    },
    DomFact {
        fact: crate::ast::fact::ForallFact,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    ThenFact {
        fact: crate::ast::fact::ForallFact,
        failed_index: usize,
        param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        succeeded_then: Vec<FactWellDefinedProof>,
        failed_then: Box<FailToVerifyFactWellDefinedResult>,
    },
}

/// The actual local-proof scope, stopped before conclusion verification.
pub struct ForallIntroductionFormationFailure {
    pub fact: crate::ast::fact::ForallFact,
    pub failure: ForallIntroductionFormationFailed,
    pub local_env: Box<ExecEnv>,
}

pub enum ForallIntroductionFormationFailed {
    Parameters(IntroduceTypedParametersFailed),
    Premise {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        failed_index: usize,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
}

/// Formation-only checks never prove or assume the consequent clauses.
pub struct ForallWellDefinedLocalFailure {
    pub fact: crate::ast::fact::ForallFact,
    pub failure: ForallWellDefinedLocalFailed,
    pub local_env: Box<ExecEnv>,
}

pub enum ForallWellDefinedLocalFailed {
    Parameters(VerifyAndDefineWdParametersFailed),
    AutoOpen {
        introduced_params: IntroduceTypedParametersResult,
        opened_before_fail: Vec<crate::execute::ReleaseOneStructLayerProof>,
        failed: crate::execute::FailToReleaseOneStructLayer,
    },
    Premise {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        failed_index: usize,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    Conclusion {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        checked_then: Vec<FactWellDefinedProof>,
        failed_index: usize,
        failed_then: Box<FailToVerifyFactWellDefinedResult>,
    },
}

impl FailToVerifyForallFactWellDefinedResult {
    pub fn fact(&self) -> &crate::ast::fact::ForallFact {
        match self {
            Self::LocalIntroduction(local) => &local.fact,
            Self::LocalWellDefinedness(local) => &local.fact,
            Self::ParamType { fact, .. }
            | Self::AutoOpenStructLayer { fact, .. }
            | Self::DomFact { fact, .. }
            | Self::ThenFact { fact, .. } => fact,
        }
    }
}

// Stage order: param types/bindings → one struct layer → dom facts → then facts.
pub enum ForallFactWellDefinedProof {
    Compact(CompactForallFactWellDefinedProof),
    Normal(NormalForallFactWellDefinedProof),
    Detailed(Box<DetailedForallFactWellDefinedProof>),
}

pub struct CompactForallFactWellDefinedProof {}
pub struct NormalForallFactWellDefinedProof {}
pub struct DetailedForallFactWellDefinedProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub then: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

impl ForallFactWellDefinedProof {
    pub(crate) fn new(
        detail: OutputDetail,
        build: impl FnOnce() -> DetailedForallFactWellDefinedProof,
    ) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactForallFactWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalForallFactWellDefinedProof {}),
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

    pub fn into_compact(self) -> RuntimeResult<CompactForallFactWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "quantified WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalForallFactWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "quantified WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_detailed(self) -> RuntimeResult<DetailedForallFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(*proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedForallFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedForallFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "quantified WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub(crate) fn detailed_ref(&self) -> &DetailedForallFactWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }
}

pub enum VerifyForallFactWellDefinedResult {
    Success(ForallFactWellDefinedProof),
    Failed(FailToVerifyForallFactWellDefinedResult),
}

impl VerifyForallFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
