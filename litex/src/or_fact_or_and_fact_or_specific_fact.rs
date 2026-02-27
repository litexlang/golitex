use crate::or_fact::OrFact;
use crate::and_fact::AndFact;
use crate::specific_fact::SpecFact;
use std::fmt;
use crate::helper::str_with_line_file;

pub enum OrFactOrAndFactOrSpecFact {
    OrFact(OrFact),
    AndFact(AndFact),
    SpecFact(SpecFact)
}

impl fmt::Display for OrFactOrAndFactOrSpecFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => write!(f, "{}", or_fact),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => write!(f, "{}", and_fact),
            OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => write!(f, "{}", spec_fact),
        }
    }
}

impl OrFactOrAndFactOrSpecFact {
    pub fn line(&self) -> u32 {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => or_fact.line(),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => and_fact.line(),
            OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => spec_fact.line(),
        }
    }

    pub fn file_index(&self) -> usize {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => or_fact.file_index(),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => and_fact.file_index(),
            OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => spec_fact.file_index(),
        }
    }

    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line(), self.file_index());
    }
}

