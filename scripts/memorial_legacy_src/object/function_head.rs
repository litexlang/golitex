use crate::prelude::*;
use std::fmt;

/// Function-application head: plain identifier pieces, symbol-bound parameter
/// binders, and the few structured objects that are deliberately callable.
#[derive(Clone)]
pub enum FnObjHead {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Bound(BoundParamObj),
    /// Anonymous function literal used as applied head, e.g. `fn(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    FiniteSeqListObj(FiniteSeqListObj),
    ObjAtIndex(ObjAtIndex),
    ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
    /// A matrix operator expression used as a two-argument function, e.g. `(A '+ B)(i, j)`.
    MatrixOperator(Box<Obj>),
}

impl fmt::Display for FnObjHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            FnObjHead::Identifier(x) => write!(f, "{}", x),
            FnObjHead::IdentifierWithMod(x) => write!(f, "{}", x),
            FnObjHead::Bound(p) => write!(f, "{}", p),
            FnObjHead::AnonymousFnLiteral(a) => write!(f, "{}", a),
            FnObjHead::FiniteSeqListObj(v) => write!(f, "{}", v),
            FnObjHead::ObjAtIndex(v) => write!(f, "{}", v),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => write!(f, "{}", v),
            FnObjHead::InstantiatedTemplateObj(t) => write!(f, "{}", t),
            FnObjHead::MatrixOperator(matrix) => write!(f, "({})", matrix),
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
                AtomObj::Bound(p) => Some(FnObjHead::Bound(p)),
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
            Obj::MatrixAdd(_)
            | Obj::MatrixSub(_)
            | Obj::MatrixMul(_)
            | Obj::MatrixScalarMul(_)
            | Obj::MatrixPow(_) => Some(FnObjHead::MatrixOperator(Box::new(obj))),
            _ => None,
        }
    }
}

impl From<BoundParamObj> for FnObjHead {
    fn from(p: BoundParamObj) -> Self {
        FnObjHead::Bound(p)
    }
}

impl From<FnObjHead> for Obj {
    fn from(h: FnObjHead) -> Self {
        match h {
            FnObjHead::Identifier(x) => x.into(),
            FnObjHead::IdentifierWithMod(x) => x.into(),
            FnObjHead::Bound(p) => p.into(),
            FnObjHead::AnonymousFnLiteral(a) => (*a).clone().into(),
            FnObjHead::FiniteSeqListObj(v) => v.into(),
            FnObjHead::ObjAtIndex(v) => v.into(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => v.into(),
            FnObjHead::InstantiatedTemplateObj(t) => t.into(),
            FnObjHead::MatrixOperator(matrix) => (*matrix).clone(),
        }
    }
}
