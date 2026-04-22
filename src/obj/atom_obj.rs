use crate::prelude::*;
use std::fmt;

/// 仅「名字/绑定子」的 [`Obj`] 载荷：标识符、带 `::` 的名字、与解析期自由参标记。
#[derive(Clone)]
pub enum AtomObj {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Forall(ForallFreeParamObj),
    Def(DefHeaderFreeParamObj),
    Exist(ExistFreeParamObj),
    SetBuilder(SetBuilderFreeParamObj),
    FnSet(FnSetFreeParamObj),
    Sum(SumFreeParamObj),
    Induc(ByInducFreeParamObj),
    DefAlgo(DefAlgoFreeParamObj),
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
            AtomObj::Sum(x) => write!(f, "{}", x),
            AtomObj::Induc(x) => write!(f, "{}", x),
            AtomObj::DefAlgo(x) => write!(f, "{}", x),
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
            AtomObj::Sum(p) => {
                let name = if p.name == from {
                    to.to_string()
                } else {
                    p.name
                };
                AtomObj::Sum(SumFreeParamObj::new(name))
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
        }
    }
}

impl From<AtomObj> for Obj {
    fn from(a: AtomObj) -> Self {
        Obj::Atom(a)
    }
}
