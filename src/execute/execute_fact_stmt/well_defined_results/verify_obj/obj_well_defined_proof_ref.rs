use super::{
    CompactObjWellDefinedProof, DetailedObjWellDefinedProof, FnObjDomainFnSetEvidence,
    NormalObjWellDefinedProof, ObjWellDefinedComputation, ObjWellDefinedProofByDef,
};
use crate::ast::obj::{FnSet, Obj};

/// Borrow computation from a checked WD result without changing its mode,
/// manufacturing a proof, or allocating an adapter result.
#[derive(Clone, Copy)]
pub(crate) enum ObjWellDefinedProofRef<'a> {
    Compact(&'a CompactObjWellDefinedProof),
    Normal(&'a NormalObjWellDefinedProof),
    Detailed(&'a DetailedObjWellDefinedProof),
}

impl<'a> ObjWellDefinedProofRef<'a> {
    pub(crate) fn matches_application(self, obj: &Obj) -> bool {
        let computation = match self {
            Self::Compact(proof) => proof.computation.as_deref(),
            Self::Normal(proof) => proof.computation.as_deref(),
            Self::Detailed(proof) => return proof.obj() == obj,
        };
        match computation {
            Some(ObjWellDefinedComputation::Application(proof)) => &proof.application == obj,
            Some(ObjWellDefinedComputation::Composition(_)) | None => !matches!(obj, Obj::FnObj(_)),
        }
    }

    pub(crate) fn application_domain(self) -> Option<&'a FnSet> {
        let computation = match self {
            Self::Compact(proof) => proof.computation.as_deref(),
            Self::Normal(proof) => proof.computation.as_deref(),
            Self::Detailed(proof) => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(proof),
                    ..
                } = proof
                else {
                    return None;
                };
                return match proof.domain_fn_set.as_ref()? {
                    FnObjDomainFnSetEvidence::MultivariableSelector(source) => {
                        Some(&source.signature)
                    }
                    FnObjDomainFnSetEvidence::Matrix(source) => Some(&source.function.body),
                    FnObjDomainFnSetEvidence::Composition(source) => Some(&source.function.body),
                    FnObjDomainFnSetEvidence::FiniteFunction(source) => Some(&source.signature),
                    FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
                    | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }
                    | FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. } => Some(fn_set),
                };
            }
        }?;
        match computation {
            ObjWellDefinedComputation::Application(proof) => proof.domain.as_ref(),
            ObjWellDefinedComputation::Composition(_) => None,
        }
    }
}
