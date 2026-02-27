use std::fmt;

pub enum Atom {
    AtomWithoutPkg(AtomWithoutPkg),
    AtomWithPkg(AtomWithPkg),
}

pub struct AtomWithoutPkg {
    pub name: String,
}

pub struct AtomWithPkg {
    pub pkg: String,
    pub name: String,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::AtomWithoutPkg(atom) => write!(f, "{}", atom),
            Atom::AtomWithPkg(atom) => write!(f, "{}", atom),
        }
    }
}

impl AtomWithoutPkg {
    pub fn new(name: &str) -> Self {
        AtomWithoutPkg { name: name.to_string() }
    }
}

impl AtomWithPkg {
    pub fn new(pkg: &str, name: &str) -> Self {
        AtomWithPkg { pkg: pkg.to_string(), name: name.to_string() }
    }
}
