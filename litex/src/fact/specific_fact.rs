// use std::fmt;
// use super::atomic_fact::AtomicFact;
// use super::exist_fact::ExistFact;

// #[derive(Clone)]
// pub enum SpecFact {
//     AtomicFact(AtomicFact),
//     ExistFact(ExistFact),
// }

// impl fmt::Display for SpecFact {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             SpecFact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
//             SpecFact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
//         }
//     }
// }
