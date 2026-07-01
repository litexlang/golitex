use super::free_param_obj::DefStructFieldFreeParamObj;
use crate::prelude::*;
use std::fmt;

/// Object payloads that are represented by a name or parsing-time binder marker.
#[derive(Clone)]
pub enum AtomObj {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Forall(ForallFreeParamObj),
    Def(DefHeaderFreeParamObj),
    Exist(ExistFreeParamObj),
    SetBuilder(SetBuilderFreeParamObj),
    FnSet(FnSetFreeParamObj),
    Induc(ByInducFreeParamObj),
    DefAlgo(DefAlgoFreeParamObj),
    DefStructField(DefStructFieldFreeParamObj),
    TupleIndex(TupleIndexFreeParamObj),
    CartIndex(CartIndexFreeParamObj),
}

impl fmt::Display for AtomObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AtomObj::Identifier(x) => write!(f, "{}", x),
            AtomObj::IdentifierWithMod(x) => write!(f, "{}", x),
            AtomObj::Forall(x) => write!(f, "{}", x),
            AtomObj::Def(x) => write!(f, "{}", x),
            AtomObj::Exist(x) => write!(f, "{}", x),
            AtomObj::SetBuilder(x) => write!(f, "{}", x),
            AtomObj::FnSet(x) => write!(f, "{}", x),
            AtomObj::Induc(x) => write!(f, "{}", x),
            AtomObj::DefAlgo(x) => write!(f, "{}", x),
            AtomObj::DefStructField(x) => write!(f, "{}", x),
            AtomObj::TupleIndex(x) => write!(f, "{}", x),
            AtomObj::CartIndex(x) => write!(f, "{}", x),
        }
    }
}

impl AtomObj {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        match self {
            AtomObj::Identifier(i) => {
                if i.name == from {
                    AtomObj::Identifier(Identifier::new(to.to_string()))
                } else {
                    AtomObj::Identifier(i)
                }
            }
            AtomObj::IdentifierWithMod(m) => {
                let name = if m.name == from {
                    to.to_string()
                } else {
                    m.name
                };
                AtomObj::IdentifierWithMod(IdentifierWithMod::new(m.mod_name, name))
            }
            AtomObj::Forall(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::Forall(ForallFreeParamObj::new(name))
            }
            AtomObj::Def(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::Def(DefHeaderFreeParamObj::new(name))
            }
            AtomObj::Exist(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::Exist(ExistFreeParamObj::new(name))
            }
            AtomObj::SetBuilder(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::SetBuilder(SetBuilderFreeParamObj::new(name))
            }
            AtomObj::FnSet(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::FnSet(FnSetFreeParamObj::new(name))
            }
            AtomObj::Induc(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::Induc(ByInducFreeParamObj::new(name))
            }
            AtomObj::DefAlgo(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::DefAlgo(DefAlgoFreeParamObj::new(name))
            }
            AtomObj::DefStructField(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::DefStructField(DefStructFieldFreeParamObj::new(name))
            }
            AtomObj::TupleIndex(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::TupleIndex(TupleIndexFreeParamObj::new(name))
            }
            AtomObj::CartIndex(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::CartIndex(CartIndexFreeParamObj::new(name))
            }
        }
    }
}

impl From<AtomObj> for Obj {
    fn from(a: AtomObj) -> Self {
        Obj::Atom(a)
    }
}
