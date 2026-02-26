use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;

pub enum SpecFact {
    AtomicFact(Box<AtomicFact>),
    ExistFact(Box<ExistFact>),
}

impl fmt::Display for SpecFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpecFact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            SpecFact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
        }
    }
}