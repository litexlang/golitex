use crate::prelude::*;
use std::fmt;

/// Function-application head: plain identifier/field pieces or tagged free-parameter binders.
#[derive(Clone)]
pub enum FnObjHead {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    FieldAccess(FieldAccess),
    FieldAccessWithMod(FieldAccessWithMod),
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
            FnObjHead::Identifier(x) => write!(f, "{}", x),
            FnObjHead::IdentifierWithMod(x) => write!(f, "{}", x),
            FnObjHead::FieldAccess(x) => write!(f, "{}", x),
            FnObjHead::FieldAccessWithMod(x) => write!(f, "{}", x),
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

impl FnObjHead {
    /// If `obj` is a plain name/field shape, returns the corresponding function head; otherwise `None`.
    pub fn from_name_obj(obj: Obj) -> Option<FnObjHead> {
        match obj {
            Obj::FieldAccess(x) => Some(FnObjHead::FieldAccess(x)),
            Obj::FieldAccessWithMod(x) => Some(FnObjHead::FieldAccessWithMod(x)),
            Obj::ForallFieldAccessObj(p) => Some(FnObjHead::ForallFieldAccess(p)),
            Obj::DefFreeFieldAccessObj(p) => Some(FnObjHead::DefHeaderFieldAccess(p)),
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
                AtomObj::StructSelfField(p) => Some(FnObjHead::StructSelfField(p)),
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
            FnObjHead::Identifier(x) => x.into(),
            FnObjHead::IdentifierWithMod(x) => x.into(),
            FnObjHead::FieldAccess(x) => x.into(),
            FnObjHead::FieldAccessWithMod(x) => x.into(),
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
