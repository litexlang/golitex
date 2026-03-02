use std::fmt;

pub enum Atom {
    AtomWithoutModName(AtomWithoutModName),
    AtomWithModName(AtomWithModName),
}

pub struct AtomWithoutModName {
    pub name: String,
}

pub struct AtomWithModName {
    pub mod_name: String,
    pub name: String,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::AtomWithoutModName(atom) => write!(f, "{}", atom),
            Atom::AtomWithModName(atom) => write!(f, "{}", atom),
        }
    }
}

impl AtomWithoutModName {
    pub fn new(name: &str) -> Self {
        AtomWithoutModName { name: name.to_string() }
    }
}

impl AtomWithModName {
    pub fn new(mod_name: &str, name: &str) -> Self {
        AtomWithModName { mod_name: mod_name.to_string(), name: name.to_string() }
    }
}
