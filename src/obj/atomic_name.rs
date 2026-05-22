use crate::common::keywords::MOD_SIGN;
use std::fmt;

// Used for prop predicate and struct names.
#[derive(Clone, PartialEq, Eq)]
pub enum AtomicName {
    WithoutMod(String),
    WithMod(String, String), // mod_name, name
}

impl fmt::Display for AtomicName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AtomicName::WithoutMod(name) => write!(f, "{}", name),
            AtomicName::WithMod(mod_name, name) => {
                write!(f, "{}{}{}", mod_name, MOD_SIGN, name)
            }
        }
    }
}
