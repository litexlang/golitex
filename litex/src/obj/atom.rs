use std::fmt;
use crate::common::keywords::{DOT_AKA_FIELD_ACCESS_SIGN, MOD_SING};

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

impl Atom {
    /// 转为 IdentifierOrIdentifierWithMod：Identifier/IdentifierWithMod 直接映射，FieldAccess/FieldAccessWithMod 用整体字符串作 Identifier。
    pub fn to_identifier_or_identifier_with_mod(&self) -> IdentifierOrIdentifierWithMod {
        match self {
            Atom::IdentifierAtom(i) => IdentifierOrIdentifierWithMod::Identifier(Identifier::new(&i.name)),
            Atom::IdentifierWithMod(m) => IdentifierOrIdentifierWithMod::IdentifierWithMod(IdentifierWithMod::new(&m.mod_name, &m.name)),
            Atom::FieldAccess(fa) => IdentifierOrIdentifierWithMod::Identifier(Identifier::new(&fa.to_string())),
            Atom::FieldAccessWithMod(fa) => IdentifierOrIdentifierWithMod::Identifier(Identifier::new(&fa.to_string())),
        }
    }
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
    pub fn new(name: &str) -> Self {
        Identifier { name: name.to_string() }
    }
}

impl IdentifierWithMod {
    pub fn new(mod_name: &str, name: &str) -> Self {
        IdentifierWithMod { mod_name: mod_name.to_string(), name: name.to_string() }
    }
}

impl FieldAccess {
    pub fn new(name: &str, fields: Vec<String>) -> Self {
        FieldAccess { name: name.to_string(), fields }
    }
}

impl FieldAccessWithMod {
    pub fn new(mod_name: &str, name: &str, fields: Vec<String>) -> Self {
        FieldAccessWithMod { mod_name: mod_name.to_string(), name: name.to_string(), fields }
    }
}

impl fmt::Display for FieldAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.name, DOT_AKA_FIELD_ACCESS_SIGN, self.fields.join(DOT_AKA_FIELD_ACCESS_SIGN))
    }
}

impl fmt::Display for FieldAccessWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}{}", self.mod_name, MOD_SING, self.name, DOT_AKA_FIELD_ACCESS_SIGN, self.fields.join(DOT_AKA_FIELD_ACCESS_SIGN))
    }
}