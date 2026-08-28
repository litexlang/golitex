use super::parameter::BoundParamObj;
use crate::prelude::*;
use std::fmt;

/// Object payloads that are represented by a name or parsing-time binder marker.
#[derive(Clone)]
pub enum AtomObj {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Bound(BoundParamObj),
}

impl fmt::Display for AtomObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            AtomObj::Identifier(x) => write!(f, "{}", x),
            AtomObj::IdentifierWithMod(x) => write!(f, "{}", x),
            AtomObj::Bound(x) => write!(f, "{}", x),
        }
    }
}

impl AtomObj {
    pub fn symbol_ref(&self) -> Option<&SymbolRef> {
        match self {
            AtomObj::Identifier(identifier) => identifier.symbol.as_ref(),
            AtomObj::IdentifierWithMod(identifier) => identifier.symbol.as_ref(),
            AtomObj::Bound(param) => Some(&param.symbol),
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
            AtomObj::Bound(p) => {
                let symbol = if p.name() == from {
                    p.symbol.with_display_name(to.to_string())
                } else {
                    p.symbol
                };
                AtomObj::Bound(BoundParamObj::new(symbol))
            }
        }
    }
}

impl From<AtomObj> for Obj {
    fn from(a: AtomObj) -> Self {
        Obj::Atom(a)
    }
}
