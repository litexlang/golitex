use crate::common::keywords::MOD_SIGN;
use std::fmt;

// 用于 prop 的 predicate， struct 和 family 的名字
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
