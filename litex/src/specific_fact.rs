use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;
use crate::helper::str_with_line_file;

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
    pub fn line(&self) -> u32 {
        match self {
            SpecFact::AtomicFact(atomic_fact) => atomic_fact.line(),
            SpecFact::ExistFact(exist_fact) => exist_fact.line(),
        }
    }

    pub fn file_index(&self) -> usize {
        match self {
            SpecFact::AtomicFact(atomic_fact) => atomic_fact.file_index(),
            SpecFact::ExistFact(exist_fact) => exist_fact.file_index(),
        }
    }
}

impl SpecFact {
    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line(), self.file_index());
    }
}