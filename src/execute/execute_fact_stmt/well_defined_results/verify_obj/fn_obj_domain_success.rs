use super::{FnObjArgumentScope, ObjWellDefinedProof};
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub enum FnObjDomainSuccess {
    Compact(CompactFnObjDomainSuccess),
    Normal(NormalFnObjDomainSuccess),
    Detailed(DetailedFnObjDomainSuccess),
}

pub struct CompactFnObjDomainSuccess {}
pub struct NormalFnObjDomainSuccess {}
pub struct DetailedFnObjDomainSuccess {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub argument_scope: Option<FnObjArgumentScope>,
}

impl FnObjDomainSuccess {
    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }
    pub fn into_normal(self) -> RuntimeResult<NormalFnObjDomainSuccess> {
        OutputDetail::Normal.require(self.detail(), "function argument check")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn into_compact(self) -> RuntimeResult<CompactFnObjDomainSuccess> {
        OutputDetail::Compact.require(self.detail(), "function argument check")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn as_detailed(&self) -> RuntimeResult<&DetailedFnObjDomainSuccess> {
        OutputDetail::Detailed.require(self.detail(), "function argument check")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedFnObjDomainSuccess> {
        OutputDetail::Detailed.require(self.detail(), "function argument check")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub(crate) fn detailed_ref(&self) -> &DetailedFnObjDomainSuccess {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }
}
