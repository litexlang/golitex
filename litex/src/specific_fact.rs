use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;

#[derive(Clone)]
pub enum SpecFact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
}

impl fmt::Display for SpecFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpecFact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            SpecFact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
        }
    }
}

impl SpecFact {
    pub fn key(&self) -> String {
        match self {
            SpecFact::AtomicFact(atomic_fact) => atomic_fact.key(),
            SpecFact::ExistFact(exist_fact) => exist_fact.key(),
        }
    }
}