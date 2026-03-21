use std::fmt;
use crate::common::keywords::{DOT_AKA_FIELD_ACCESS_SIGN, MOD_SIGN};

#[derive(Clone)]
pub enum Atom {
    IdentifierAtom(Identifier),
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

#[derive(Clone)]
pub struct IdentifierWithMod {
    pub mod_name: String,
    pub name: String,
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
            Atom::IdentifierAtom(atom) => write!(f, "{}", atom),
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
        FieldAccessWithMod { mod_name, name, fields }
    }
}

impl fmt::Display for FieldAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.name, DOT_AKA_FIELD_ACCESS_SIGN, self.fields.join(DOT_AKA_FIELD_ACCESS_SIGN))
    }
}

impl fmt::Display for FieldAccessWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}{}", self.mod_name, MOD_SIGN, self.name, DOT_AKA_FIELD_ACCESS_SIGN, self.fields.join(DOT_AKA_FIELD_ACCESS_SIGN))
    }
}