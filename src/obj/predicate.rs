use crate::common::keywords::MOD_SIGN;
use std::fmt;

#[derive(Clone, PartialEq, Eq)]
pub enum PredicateType {
    WithoutMod(String),
    WithMod(String, String),
}

impl fmt::Display for PredicateType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PredicateType::WithoutMod(name) => write!(f, "{}", name),
            PredicateType::WithMod(mod_name, name) => {
                write!(f, "{}{}{}", mod_name, MOD_SIGN, name)
            }
        }
    }
}
