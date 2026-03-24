use crate::common::keywords::{DOT_AKA_FIELD_ACCESS_SIGN, MOD_SIGN};
use crate::obj::Number;
use std::fmt;

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
    pub normalized_calculated_value: Option<Number>,
}

pub fn identifier_to_string(name: &str) -> String {
    name.to_string()
}

#[derive(Clone)]
pub struct IdentifierWithMod {
    pub mod_name: String,
    pub name: String,
    pub normalized_calculated_value: Option<Number>,
}

pub fn identifier_with_mod_to_string(mod_name: &str, name: &str) -> String {
    format!("{}{}{}", mod_name, MOD_SIGN, name)
}

#[derive(Clone)]
pub struct FieldAccess {
    pub name: String,
    pub fields: Vec<String>,
    pub normalized_calculated_value: Option<Number>,
}

#[derive(Clone)]
pub struct FieldAccessWithMod {
    pub mod_name: String,
    pub name: String,
    pub fields: Vec<String>,
    pub normalized_calculated_value: Option<Number>,
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
    pub fn new(name: String, calculated_value: Option<Number>) -> Self {
        Identifier {
            name,
            normalized_calculated_value: calculated_value,
        }
    }
}

impl IdentifierWithMod {
    pub fn new(mod_name: String, name: String, calculated_value: Option<Number>) -> Self {
        IdentifierWithMod {
            mod_name,
            name,
            normalized_calculated_value: calculated_value,
        }
    }
}

impl FieldAccess {
    pub fn new(name: String, fields: Vec<String>, calculated_value: Option<Number>) -> Self {
        FieldAccess {
            name,
            fields,
            normalized_calculated_value: calculated_value,
        }
    }
}

impl FieldAccessWithMod {
    pub fn new(
        mod_name: String,
        name: String,
        fields: Vec<String>,
        calculated_value: Option<Number>,
    ) -> Self {
        FieldAccessWithMod {
            mod_name,
            name,
            fields,
            normalized_calculated_value: calculated_value,
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
