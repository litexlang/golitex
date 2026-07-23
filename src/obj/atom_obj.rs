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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
    pub(crate) fn symbol_ref(&self) -> Option<&SymbolRef> {
        match self {
            AtomObj::Identifier(identifier) => identifier.symbol.as_ref(),
            AtomObj::IdentifierWithMod(identifier) => identifier.symbol.as_ref(),
            AtomObj::Forall(param) => Some(&param.symbol),
            AtomObj::Def(param) => Some(&param.symbol),
            AtomObj::Exist(param) => Some(&param.symbol),
            AtomObj::SetBuilder(param) => Some(&param.symbol),
            AtomObj::FnSet(param) => Some(&param.symbol),
            AtomObj::Induc(param) => Some(&param.symbol),
            AtomObj::DefAlgo(param) => Some(&param.symbol),
            AtomObj::DefStructField(param) => Some(&param.symbol),
            AtomObj::TupleIndex(param) => Some(&param.symbol),
            AtomObj::CartIndex(param) => Some(&param.symbol),
        }
    }

    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        match self {
            AtomObj::Identifier(i) => {
                if i.name == from {
                    let renamed = match i.symbol {
                        Some(symbol) => Identifier::new_bound(
                            to.to_string(),
                            symbol.with_display_name(to.to_string()),
                        ),
                        None => Identifier::new(to.to_string()),
                    };
                    AtomObj::Identifier(renamed)
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
                let renamed = match m.symbol {
                    Some(symbol) => IdentifierWithMod::new_bound(
                        m.mod_name,
                        name.clone(),
                        symbol.with_display_name(name),
                    ),
                    None => IdentifierWithMod::new(m.mod_name, name),
                };
                AtomObj::IdentifierWithMod(renamed)
            }
            AtomObj::Forall(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::Forall(ForallFreeParamObj::new(symbol))
            }
            AtomObj::Def(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::Def(DefHeaderFreeParamObj::new(symbol))
            }
            AtomObj::Exist(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::Exist(ExistFreeParamObj::new(symbol))
            }
            AtomObj::SetBuilder(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::SetBuilder(SetBuilderFreeParamObj::new(symbol))
            }
            AtomObj::FnSet(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::FnSet(FnSetFreeParamObj::new(symbol))
            }
            AtomObj::Induc(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::Induc(ByInducFreeParamObj::new(symbol))
            }
            AtomObj::DefAlgo(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::DefAlgo(DefAlgoFreeParamObj::new(symbol))
            }
            AtomObj::DefStructField(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::DefStructField(DefStructFieldFreeParamObj::new(symbol))
            }
            AtomObj::TupleIndex(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::TupleIndex(TupleIndexFreeParamObj::new(symbol))
            }
            AtomObj::CartIndex(p) => {
                let symbol = if p.name == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::CartIndex(CartIndexFreeParamObj::new(symbol))
            }
        }
    }
}

impl From<AtomObj> for Obj {
    fn from(a: AtomObj) -> Self {
        Obj::Atom(a)
    }
}
