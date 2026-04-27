use crate::prelude::*;
use std::fmt;

/// Function-application head: plain identifier pieces or tagged free-parameter binders.
#[derive(Clone)]
pub enum FnObjHead {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Forall(ForallFreeParamObj),
    DefHeader(DefHeaderFreeParamObj),
    Exist(ExistFreeParamObj),
    SetBuilder(SetBuilderFreeParamObj),
    FnSet(FnSetFreeParamObj),
    /// Anonymous function literal used as applied head, e.g. `'(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    Induc(ByInducFreeParamObj),
    DefAlgo(DefAlgoFreeParamObj),
}

impl fmt::Display for FnObjHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FnObjHead::Identifier(x) => write!(f, "{}", x),
            FnObjHead::IdentifierWithMod(x) => write!(f, "{}", x),
            FnObjHead::Forall(p) => write!(f, "{}", p),
            FnObjHead::DefHeader(p) => write!(f, "{}", p),
            FnObjHead::Exist(p) => write!(f, "{}", p),
            FnObjHead::SetBuilder(p) => write!(f, "{}", p),
            FnObjHead::FnSet(p) => write!(f, "{}", p),
            FnObjHead::AnonymousFnLiteral(a) => write!(f, "{}", a),
            FnObjHead::Induc(p) => write!(f, "{}", p),
            FnObjHead::DefAlgo(p) => write!(f, "{}", p),
        }
    }
}

impl FnObjHead {
    /// If `obj` is a plain name shape, returns the corresponding function head; otherwise `None`.
    pub fn from_name_obj(obj: Obj) -> Option<FnObjHead> {
        match obj {
            Obj::Atom(a) => match a {
                AtomObj::Identifier(x) => Some(FnObjHead::Identifier(x)),
                AtomObj::IdentifierWithMod(x) => Some(FnObjHead::IdentifierWithMod(x)),
                AtomObj::Forall(p) => Some(FnObjHead::Forall(p)),
                AtomObj::Def(p) => Some(FnObjHead::DefHeader(p)),
                AtomObj::Exist(p) => Some(FnObjHead::Exist(p)),
                AtomObj::SetBuilder(p) => Some(FnObjHead::SetBuilder(p)),
                AtomObj::FnSet(p) => Some(FnObjHead::FnSet(p)),
                AtomObj::Induc(p) => Some(FnObjHead::Induc(p)),
                AtomObj::DefAlgo(p) => Some(FnObjHead::DefAlgo(p)),
            },
            _ => None,
        }
    }
}

impl From<ForallFreeParamObj> for FnObjHead {
    fn from(p: ForallFreeParamObj) -> Self {
        FnObjHead::Forall(p)
    }
}

impl From<DefHeaderFreeParamObj> for FnObjHead {
    fn from(p: DefHeaderFreeParamObj) -> Self {
        FnObjHead::DefHeader(p)
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

impl From<FnObjHead> for Obj {
    fn from(h: FnObjHead) -> Self {
        match h {
            FnObjHead::Identifier(x) => x.into(),
            FnObjHead::IdentifierWithMod(x) => x.into(),
            FnObjHead::Forall(p) => p.into(),
            FnObjHead::DefHeader(p) => p.into(),
            FnObjHead::Exist(p) => p.into(),
            FnObjHead::SetBuilder(p) => p.into(),
            FnObjHead::FnSet(p) => p.into(),
            FnObjHead::AnonymousFnLiteral(a) => (*a).clone().into(),
            FnObjHead::Induc(p) => p.into(),
            FnObjHead::DefAlgo(p) => p.into(),
        }
    }
}
