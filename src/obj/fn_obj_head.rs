use crate::prelude::*;
use std::fmt;

/// Function-application head: plain identifier pieces, tagged free-parameter
/// binders, and the few structured objects that are deliberately callable.
#[derive(Clone)]
pub enum FnObjHead {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Forall(ForallFreeParamObj),
    DefHeader(DefHeaderFreeParamObj),
    Exist(ExistFreeParamObj),
    SetBuilder(SetBuilderFreeParamObj),
    FnSet(FnSetFreeParamObj),
    DefStructField(DefStructFieldFreeParamObj),
    /// Anonymous function literal used as applied head, e.g. `fn(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    FiniteSeqListObj(FiniteSeqListObj),
    ObjAtIndex(ObjAtIndex),
    ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess),
    Induc(ByInducFreeParamObj),
    DefAlgo(DefAlgoFreeParamObj),
    TupleIndex(TupleIndexFreeParamObj),
    CartIndex(CartIndexFreeParamObj),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
}

impl fmt::Display for FnObjHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            FnObjHead::Identifier(x) => write!(f, "{}", x),
            FnObjHead::IdentifierWithMod(x) => write!(f, "{}", x),
            FnObjHead::Forall(p) => write!(f, "{}", p),
            FnObjHead::DefHeader(p) => write!(f, "{}", p),
            FnObjHead::Exist(p) => write!(f, "{}", p),
            FnObjHead::SetBuilder(p) => write!(f, "{}", p),
            FnObjHead::FnSet(p) => write!(f, "{}", p),
            FnObjHead::DefStructField(p) => write!(f, "{}", p),
            FnObjHead::AnonymousFnLiteral(a) => write!(f, "{}", a),
            FnObjHead::FiniteSeqListObj(v) => write!(f, "{}", v),
            FnObjHead::ObjAtIndex(v) => write!(f, "{}", v),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => write!(f, "{}", v),
            FnObjHead::Induc(p) => write!(f, "{}", p),
            FnObjHead::DefAlgo(p) => write!(f, "{}", p),
            FnObjHead::TupleIndex(p) => write!(f, "{}", p),
            FnObjHead::CartIndex(p) => write!(f, "{}", p),
            FnObjHead::InstantiatedTemplateObj(t) => write!(f, "{}", t),
        }
    }
}

impl FnObjHead {
    /// If `obj` is a plain name shape, returns the corresponding function head; otherwise `None`.
    pub fn given_an_atom_return_a_fn_obj_head(obj: Obj) -> Option<FnObjHead> {
        match obj {
            Obj::Atom(a) => match a {
                AtomObj::Identifier(x) => Some(FnObjHead::Identifier(x)),
                AtomObj::IdentifierWithMod(x) => Some(FnObjHead::IdentifierWithMod(x)),
                AtomObj::Forall(p) => Some(FnObjHead::Forall(p)),
                AtomObj::Def(p) => Some(FnObjHead::DefHeader(p)),
                AtomObj::Exist(p) => Some(FnObjHead::Exist(p)),
                AtomObj::SetBuilder(p) => Some(FnObjHead::SetBuilder(p)),
                AtomObj::FnSet(p) => Some(FnObjHead::FnSet(p)),
                AtomObj::DefStructField(p) => Some(FnObjHead::DefStructField(p)),
                AtomObj::Induc(p) => Some(FnObjHead::Induc(p)),
                AtomObj::DefAlgo(p) => Some(FnObjHead::DefAlgo(p)),
                AtomObj::TupleIndex(p) => Some(FnObjHead::TupleIndex(p)),
                AtomObj::CartIndex(p) => Some(FnObjHead::CartIndex(p)),
            },
            _ => None,
        }
    }

    /// Return a function head for object shapes that Litex intentionally allows as callable heads.
    pub fn from_callable_obj(obj: Obj) -> Option<FnObjHead> {
        match obj {
            Obj::Atom(_) => FnObjHead::given_an_atom_return_a_fn_obj_head(obj),
            Obj::AnonymousFn(a) => Some(FnObjHead::AnonymousFnLiteral(Box::new(a))),
            Obj::FiniteSeqListObj(v) => Some(FnObjHead::FiniteSeqListObj(v)),
            Obj::ObjAtIndex(v) => Some(FnObjHead::ObjAtIndex(v)),
            Obj::ObjAsStructInstanceWithFieldAccess(v) => {
                Some(FnObjHead::ObjAsStructInstanceWithFieldAccess(v))
            }
            Obj::InstantiatedTemplateObj(t) => Some(FnObjHead::InstantiatedTemplateObj(t)),
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

impl From<DefStructFieldFreeParamObj> for FnObjHead {
    fn from(p: DefStructFieldFreeParamObj) -> Self {
        FnObjHead::DefStructField(p)
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

impl From<TupleIndexFreeParamObj> for FnObjHead {
    fn from(p: TupleIndexFreeParamObj) -> Self {
        FnObjHead::TupleIndex(p)
    }
}

impl From<CartIndexFreeParamObj> for FnObjHead {
    fn from(p: CartIndexFreeParamObj) -> Self {
        FnObjHead::CartIndex(p)
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
            FnObjHead::DefStructField(p) => p.into(),
            FnObjHead::AnonymousFnLiteral(a) => (*a).clone().into(),
            FnObjHead::FiniteSeqListObj(v) => v.into(),
            FnObjHead::ObjAtIndex(v) => v.into(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => v.into(),
            FnObjHead::Induc(p) => p.into(),
            FnObjHead::DefAlgo(p) => p.into(),
            FnObjHead::TupleIndex(p) => p.into(),
            FnObjHead::CartIndex(p) => p.into(),
            FnObjHead::InstantiatedTemplateObj(t) => t.into(),
        }
    }
}
