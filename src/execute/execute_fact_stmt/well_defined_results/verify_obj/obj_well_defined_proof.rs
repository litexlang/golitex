use super::obj_well_defined_proof_by_def::ObjWellDefinedProofByDef;
use crate::ast::obj::{AnonymousFn, FnSet, Obj};
use crate::result_detail::OutputDetail;
use crate::runtime::{RuntimeResult, WellDefinednessId};

/// Success only. Failure remains on `VerifyObjWellDefinedResult`.
pub enum ObjWellDefinedProof {
    Compact(CompactObjWellDefinedProof),
    Normal(NormalObjWellDefinedProof),
    Detailed(Box<DetailedObjWellDefinedProof>),
}

pub struct CompactObjWellDefinedProof {
    pub computation: Option<Box<ObjWellDefinedComputation>>,
}

pub struct NormalObjWellDefinedProof {
    pub computation: Option<Box<ObjWellDefinedComputation>>,
}

pub enum ObjWellDefinedComputation {
    Application(CheckedApplicationDomain),
    Composition(AnonymousFn),
}

/// Computation consumes a checked application's selected complete domain.
/// Scalar WD acknowledgements carry neither a subject clone nor a proof tree.
pub struct CheckedApplicationDomain {
    pub application: Obj,
    pub domain: Option<FnSet>,
}

pub enum DetailedObjWellDefinedProof {
    ByKnown {
        obj: Obj,
        wd_id: WellDefinednessId,
    },
    ByDef {
        obj: Obj,
        proof: ObjWellDefinedProofByDef,
    },
}

impl ObjWellDefinedProof {
    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }

    pub fn into_compact(self) -> RuntimeResult<CompactObjWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "object WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalObjWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "object WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_detailed(self) -> RuntimeResult<DetailedObjWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "object WD")?;
        match self {
            Self::Detailed(proof) => Ok(*proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedObjWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "object WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedObjWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "object WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    /// Used only by consumers whose contract requires complete evidence.
    pub(crate) fn detailed_ref(&self) -> &DetailedObjWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }

    pub fn obj(&self) -> &Obj {
        self.detailed_ref().obj()
    }

    pub(crate) fn by_def_mut(&mut self) -> Option<&mut ObjWellDefinedProofByDef> {
        match self {
            Self::Detailed(proof) => match proof.as_mut() {
                DetailedObjWellDefinedProof::ByDef { proof, .. } => Some(proof),
                DetailedObjWellDefinedProof::ByKnown { .. } => None,
            },
            Self::Compact(_) | Self::Normal(_) => None,
        }
    }

    pub(crate) fn as_view(&self) -> super::ObjWellDefinedProofRef<'_> {
        match self {
            Self::Compact(proof) => super::ObjWellDefinedProofRef::Compact(proof),
            Self::Normal(proof) => super::ObjWellDefinedProofRef::Normal(proof),
            Self::Detailed(proof) => super::ObjWellDefinedProofRef::Detailed(proof),
        }
    }

    pub(crate) fn reduced(detail: OutputDetail, obj: &Obj, domain: Option<&FnSet>) -> Option<Self> {
        let computation = || {
            matches!(obj, Obj::FnObj(_)).then(|| {
                Box::new(ObjWellDefinedComputation::Application(
                    CheckedApplicationDomain {
                        application: obj.clone(),
                        domain: domain.cloned(),
                    },
                ))
            })
        };
        match detail {
            OutputDetail::Compact => Some(Self::Compact(CompactObjWellDefinedProof {
                computation: computation(),
            })),
            OutputDetail::Normal => Some(Self::Normal(NormalObjWellDefinedProof {
                computation: computation(),
            })),
            OutputDetail::Detailed => None,
        }
    }

    pub(crate) fn by_known(detail: OutputDetail, obj: &Obj, wd_id: WellDefinednessId) -> Self {
        Self::reduced(detail, obj, None).unwrap_or_else(|| {
            Self::Detailed(Box::new(DetailedObjWellDefinedProof::ByKnown {
                obj: obj.clone(),
                wd_id,
            }))
        })
    }

    pub(crate) fn by_def(
        detail: OutputDetail,
        obj: &Obj,
        domain: Option<&FnSet>,
        build: impl FnOnce() -> ObjWellDefinedProofByDef,
    ) -> Self {
        Self::reduced(detail, obj, domain).unwrap_or_else(|| {
            Self::Detailed(Box::new(DetailedObjWellDefinedProof::ByDef {
                obj: obj.clone(),
                proof: build(),
            }))
        })
    }

    pub(crate) fn composition(
        detail: OutputDetail,
        obj: &Obj,
        proof: crate::execute::execute_fact_stmt::function_composition::CompositionObjWellDefinedProof,
    ) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactObjWellDefinedProof {
                computation: Some(Box::new(ObjWellDefinedComputation::Composition(
                    proof.function,
                ))),
            }),
            OutputDetail::Normal => Self::Normal(NormalObjWellDefinedProof {
                computation: Some(Box::new(ObjWellDefinedComputation::Composition(
                    proof.function,
                ))),
            }),
            OutputDetail::Detailed => Self::by_def(detail, obj, None, || {
                ObjWellDefinedProofByDef::FunctionSpace(super::obj_well_defined_proof_by_def::FunctionSpaceObjWellDefinedProofByDef::Composition(proof))
            }),
        }
    }

    pub(crate) fn composition_function(&self) -> RuntimeResult<Option<&AnonymousFn>> {
        let computation = match self {
            Self::Compact(proof) => proof.computation.as_deref(),
            Self::Normal(proof) => proof.computation.as_deref(),
            Self::Detailed(proof) => return match proof.as_ref() {
                DetailedObjWellDefinedProof::ByKnown { .. } => Ok(None),
                DetailedObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::FunctionSpace(super::obj_well_defined_proof_by_def::FunctionSpaceObjWellDefinedProofByDef::Composition(proof)), .. } => Ok(Some(&proof.function)),
                _ => Err(crate::runtime::RuntimeError::InternalBug("composition WD has a different constructor".into())),
            },
        };
        match computation {
            None => Ok(None),
            Some(ObjWellDefinedComputation::Composition(function)) => Ok(Some(function)),
            Some(ObjWellDefinedComputation::Application(_)) => {
                Err(crate::runtime::RuntimeError::InternalBug(
                    "composition WD has an application payload".into(),
                ))
            }
        }
    }
}

impl DetailedObjWellDefinedProof {
    pub fn obj(&self) -> &Obj {
        match self {
            Self::ByKnown { obj, .. } | Self::ByDef { obj, .. } => obj,
        }
    }
}
