use crate::prelude::*;
use std::fmt;

/// Function-application head: plain [`Atom`] pieces or tagged free-parameter binders (not wrapped in [`Atom`]).
#[derive(Clone)]
pub enum FnObjHead {
    Atom(Atom),
    Forall(ForallFreeParamObj),
    ForallFieldAccess(ForallFieldAccessObj),
    DefHeader(DefHeaderFreeParamObj),
    DefHeaderFieldAccess(DefHeaderFreeFieldAccessObj),
    Exist(ExistFreeParamObj),
    SetBuilder(SetBuilderFreeParamObj),
    FnSet(FnSetFreeParamObj),
    Induc(ByInducFreeParamObj),
    DefAlgo(DefAlgoFreeParamObj),
    StructSelfField(StructSelfFieldFreeParamObj),
}

impl fmt::Display for FnObjHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FnObjHead::Atom(a) => write!(f, "{}", a),
            FnObjHead::Forall(p) => write!(f, "{}", p),
            FnObjHead::ForallFieldAccess(p) => write!(f, "{}", p),
            FnObjHead::DefHeader(p) => write!(f, "{}", p),
            FnObjHead::DefHeaderFieldAccess(p) => write!(f, "{}", p),
            FnObjHead::Exist(p) => write!(f, "{}", p),
            FnObjHead::SetBuilder(p) => write!(f, "{}", p),
            FnObjHead::FnSet(p) => write!(f, "{}", p),
            FnObjHead::Induc(p) => write!(f, "{}", p),
            FnObjHead::DefAlgo(p) => write!(f, "{}", p),
            FnObjHead::StructSelfField(p) => write!(f, "{}", p),
        }
    }
}

impl From<Atom> for FnObjHead {
    fn from(a: Atom) -> Self {
        FnObjHead::Atom(a)
    }
}

impl From<ForallFreeParamObj> for FnObjHead {
    fn from(p: ForallFreeParamObj) -> Self {
        FnObjHead::Forall(p)
    }
}

impl From<ForallFieldAccessObj> for FnObjHead {
    fn from(p: ForallFieldAccessObj) -> Self {
        FnObjHead::ForallFieldAccess(p)
    }
}

impl From<DefHeaderFreeParamObj> for FnObjHead {
    fn from(p: DefHeaderFreeParamObj) -> Self {
        FnObjHead::DefHeader(p)
    }
}

impl From<DefHeaderFreeFieldAccessObj> for FnObjHead {
    fn from(p: DefHeaderFreeFieldAccessObj) -> Self {
        FnObjHead::DefHeaderFieldAccess(p)
    }
}

impl From<ExistFreeParamObj> for FnObjHead {
    fn from(p: ExistFreeParamObj) -> Self {
        FnObjHead::Exist(p)
    }
}

impl From<SetBuilderFreeParamObj> for FnObjHead {
    fn from(p: SetBuilderFreeParamObj) -> Self {
        FnObjHead::SetBuilder(p)
    }
}

impl From<FnSetFreeParamObj> for FnObjHead {
    fn from(p: FnSetFreeParamObj) -> Self {
        FnObjHead::FnSet(p)
    }
}

impl From<ByInducFreeParamObj> for FnObjHead {
    fn from(p: ByInducFreeParamObj) -> Self {
        FnObjHead::Induc(p)
    }
}

impl From<DefAlgoFreeParamObj> for FnObjHead {
    fn from(p: DefAlgoFreeParamObj) -> Self {
        FnObjHead::DefAlgo(p)
    }
}

impl From<StructSelfFieldFreeParamObj> for FnObjHead {
    fn from(p: StructSelfFieldFreeParamObj) -> Self {
        FnObjHead::StructSelfField(p)
    }
}

impl From<FnObjHead> for Obj {
    fn from(h: FnObjHead) -> Self {
        match h {
            FnObjHead::Atom(a) => a.into(),
            FnObjHead::Forall(p) => p.into(),
            FnObjHead::ForallFieldAccess(p) => p.into(),
            FnObjHead::DefHeader(p) => p.into(),
            FnObjHead::DefHeaderFieldAccess(p) => p.into(),
            FnObjHead::Exist(p) => p.into(),
            FnObjHead::SetBuilder(p) => p.into(),
            FnObjHead::FnSet(p) => p.into(),
            FnObjHead::Induc(p) => p.into(),
            FnObjHead::DefAlgo(p) => p.into(),
            FnObjHead::StructSelfField(p) => p.into(),
        }
    }
}
