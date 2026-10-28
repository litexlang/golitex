use crate::ast::fact::EqualFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, CompactAtomicFactWellDefinedProof,
    DetailedAtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    NormalAtomicFactWellDefinedProof, PredicateSignatureWellDefinedProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    CompactObjWellDefinedProof, NormalObjWellDefinedProof, ObjWellDefinedProofRef,
};
use crate::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyObjWellDefinedResult, ObjWellDefinedProof,
};
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub struct FailToVerifyEqualFactWellDefinedResult {
    pub fact: EqualFact,
    pub failed_obj: crate::ast::obj::Obj,
    pub reason: FailToVerifyObjWellDefinedResult,
}

pub enum EqualFactWellDefinedProof {
    Compact(CompactEqualFactWellDefinedProof),
    Normal(NormalEqualFactWellDefinedProof),
    Detailed(Box<DetailedEqualFactWellDefinedProof>),
}

pub struct CompactEqualFactWellDefinedProof {
    pub left: CompactObjWellDefinedProof,
    pub right: CompactObjWellDefinedProof,
}
pub struct NormalEqualFactWellDefinedProof {
    pub left: NormalObjWellDefinedProof,
    pub right: NormalObjWellDefinedProof,
}
pub struct DetailedEqualFactWellDefinedProof {
    pub left: ObjWellDefinedProof,
    pub right: ObjWellDefinedProof,
}

pub enum VerifyEqualFactWellDefinedResult {
    Success(EqualFactWellDefinedProof),
    Failed(FailToVerifyEqualFactWellDefinedResult),
}

impl EqualFactWellDefinedProof {
    pub fn from_children(
        detail: OutputDetail,
        left: ObjWellDefinedProof,
        right: ObjWellDefinedProof,
    ) -> RuntimeResult<Self> {
        detail.require(left.detail(), "equality WD left")?;
        detail.require(right.detail(), "equality WD right")?;
        Ok(match detail {
            OutputDetail::Compact => Self::Compact(CompactEqualFactWellDefinedProof {
                left: left.into_compact()?,
                right: right.into_compact()?,
            }),
            OutputDetail::Normal => Self::Normal(NormalEqualFactWellDefinedProof {
                left: left.into_normal()?,
                right: right.into_normal()?,
            }),
            OutputDetail::Detailed => {
                Self::Detailed(Box::new(DetailedEqualFactWellDefinedProof { left, right }))
            }
        })
    }
    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }
    pub fn into_normal(self) -> RuntimeResult<NormalEqualFactWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "equality WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn into_compact(self) -> RuntimeResult<CompactEqualFactWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "equality WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn as_detailed(&self) -> RuntimeResult<&DetailedEqualFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "equality WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn into_detailed(self) -> RuntimeResult<DetailedEqualFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "equality WD")?;
        match self {
            Self::Detailed(proof) => Ok(*proof),
            _ => unreachable!(),
        }
    }
    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedEqualFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "equality WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub(crate) fn detailed_ref(&self) -> &DetailedEqualFactWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }
    pub(crate) fn left(&self) -> ObjWellDefinedProofRef<'_> {
        match self {
            Self::Compact(proof) => ObjWellDefinedProofRef::Compact(&proof.left),
            Self::Normal(proof) => ObjWellDefinedProofRef::Normal(&proof.left),
            Self::Detailed(proof) => proof.left.as_view(),
        }
    }
    pub(crate) fn right(&self) -> ObjWellDefinedProofRef<'_> {
        match self {
            Self::Compact(proof) => ObjWellDefinedProofRef::Compact(&proof.right),
            Self::Normal(proof) => ObjWellDefinedProofRef::Normal(&proof.right),
            Self::Detailed(proof) => proof.right.as_view(),
        }
    }
}

impl VerifyEqualFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// And/chain keep the same mode when viewing mixed atomic WD.
impl From<EqualFactWellDefinedProof> for AtomicFactWellDefinedProof {
    fn from(proof: EqualFactWellDefinedProof) -> Self {
        match proof {
            EqualFactWellDefinedProof::Compact(_) => {
                Self::Compact(CompactAtomicFactWellDefinedProof {})
            }
            EqualFactWellDefinedProof::Normal(_) => {
                Self::Normal(NormalAtomicFactWellDefinedProof {})
            }
            EqualFactWellDefinedProof::Detailed(proof) => {
                Self::Detailed(Box::new(DetailedAtomicFactWellDefinedProof {
                    well_defined_of_each_parameter: vec![proof.left, proof.right],
                    predicate_signature: PredicateSignatureWellDefinedProof::Builtin,
                    predicate_domain:
                        super::super::well_defined_result::PredicateDomainProof::ByRequirements(
                            Vec::new(),
                        ),
                }))
            }
        }
    }
}
impl From<FailToVerifyEqualFactWellDefinedResult> for FailToVerifyAtomicFactWellDefinedResult {
    fn from(fail: FailToVerifyEqualFactWellDefinedResult) -> Self {
        Self::Argument {
            fact: fail.fact.into(),
            reason: fail.reason,
        }
    }
}
