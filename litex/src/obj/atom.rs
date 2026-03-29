use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum Atom {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    FieldAccess(FieldAccess),
    FieldAccessWithMod(FieldAccessWithMod),
}

#[derive(Clone)]
pub enum IdentifierOrIdentifierWithMod {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
}

impl fmt::Display for IdentifierOrIdentifierWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IdentifierOrIdentifierWithMod::Identifier(i) => write!(f, "{}", i),
            IdentifierOrIdentifierWithMod::IdentifierWithMod(m) => write!(f, "{}", m),
        }
    }
}

impl IdentifierOrIdentifierWithMod {
    pub fn literally_the_same_as(&self, other: &IdentifierOrIdentifierWithMod) -> bool {
        return self.to_string() == other.to_string();
    }
}

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

#[derive(Clone)]
pub struct FieldAccess {
    pub name: String,
    pub fields: Vec<String>,
}

#[derive(Clone)]
pub struct FieldAccessWithMod {
    pub mod_name: String,
    pub name: String,
    pub fields: Vec<String>,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Identifier(atom) => write!(f, "{}", atom),
            Atom::IdentifierWithMod(atom) => write!(f, "{}", atom),
            Atom::FieldAccess(atom) => write!(f, "{}", atom),
            Atom::FieldAccessWithMod(atom) => write!(f, "{}", atom),
        }
    }
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

impl FieldAccess {
    pub fn new(name: String, fields: Vec<String>) -> Self {
        FieldAccess { name, fields }
    }
}

impl FieldAccessWithMod {
    pub fn new(mod_name: String, name: String, fields: Vec<String>) -> Self {
        FieldAccessWithMod {
            mod_name,
            name,
            fields,
        }
    }
}

impl fmt::Display for FieldAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", field_access_to_string(&self.name, &self.fields))
    }
}

pub fn field_access_to_string(name: &str, fields: &Vec<String>) -> String {
    format!(
        "{}{}{}",
        name,
        DOT_AKA_FIELD_ACCESS_SIGN,
        fields.join(DOT_AKA_FIELD_ACCESS_SIGN)
    )
}

impl fmt::Display for FieldAccessWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            field_access_with_mod_to_string(&self.mod_name, &self.name, &self.fields)
        )
    }
}

pub fn field_access_with_mod_to_string(mod_name: &str, name: &str, fields: &Vec<String>) -> String {
    format!(
        "{}{}{}{}{}",
        mod_name,
        MOD_SIGN,
        name,
        DOT_AKA_FIELD_ACCESS_SIGN,
        fields.join(DOT_AKA_FIELD_ACCESS_SIGN)
    )
}
