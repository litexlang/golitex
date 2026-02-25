// use std::fmt;
// use crate::consts::{PKG_SEPARATOR};

// pub enum Predicate {
//     PredicateWithoutPkg(PredicateWithoutPkg),
//     PredicateWithPkg(PredicateWithPkg),
// }

// #[allow(non_camel_case_types)]
// pub type box_Predicate = Box<Predicate>;

// pub struct PredicateWithoutPkg {
//     pub name: String,
// }

// pub struct PredicateWithPkg {
//     pub pkg: String,
//     pub name: String,
// }

// impl fmt::Display for Predicate {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             Predicate::PredicateWithoutPkg(predicate) => write!(f, "{}", predicate.name),
//             Predicate::PredicateWithPkg(predicate) => write!(f, "{}{}{}", predicate.pkg, PKG_SEPARATOR, predicate.name),
//         }
//     }
// }

// impl Predicate {
//     pub fn box_predicate_without_pkg(name: &str) -> box_Predicate {
//         Box::new(Predicate::PredicateWithoutPkg(PredicateWithoutPkg::new(name)))
//     }
//     pub fn box_predicate_with_pkg(pkg: &str, name: &str) -> box_Predicate {
//         Box::new(Predicate::PredicateWithPkg(PredicateWithPkg::new(pkg, name)))
//     }
// }

// impl PredicateWithoutPkg {
//     pub fn new(name: &str) -> Self {
//         PredicateWithoutPkg { name: name.to_string() }
//     }
// }

// impl PredicateWithPkg {
//     pub fn new(pkg: &str, name: &str) -> Self {
//         PredicateWithPkg { pkg: pkg.to_string(), name: name.to_string() }
//     }
// }