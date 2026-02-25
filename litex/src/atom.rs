use std::fmt;

pub enum Atom {
    AtomWithoutPkg(AtomWithoutPkg),
    AtomWithPkg(AtomWithPkg),
}

impl Atom {
    pub fn box_atom_without_pkg(atom: AtomWithoutPkg) -> Box<Atom> {
        Box::new(Atom::AtomWithoutPkg(atom))
    }
    pub fn box_atom_with_pkg(atom_with_pkg: AtomWithPkg) -> Box<Atom> {
        Box::new(Atom::AtomWithPkg(atom_with_pkg))
    }
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