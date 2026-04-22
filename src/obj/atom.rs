use crate::prelude::*;

#[derive(Clone)]
pub struct Identifier {
    pub name: String,
}

pub fn identifier_to_string(name: &str) -> String {
    name.to_string()
}

#[derive(Clone)]
pub struct IdentifierWithMod {
    pub mod_name: String,
    pub name: String,
}

pub fn identifier_with_mod_to_string(mod_name: &str, name: &str) -> String {
    format!("{}{}{}", mod_name, MOD_SIGN, name)
}

impl Identifier {
    pub fn new(name: String) -> Self {
        Identifier { name }
    }
}

impl IdentifierWithMod {
    pub fn new(mod_name: String, name: String) -> Self {
        IdentifierWithMod { mod_name, name }
    }
}
