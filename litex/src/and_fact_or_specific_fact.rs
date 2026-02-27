use crate::and_fact::AndFact;
use crate::specific_fact::SpecFact;
use crate::helper::str_with_line_file;
use std::fmt;

pub enum AndFactOrSpecFact {
    AndFact(AndFact),
    SpecFact(SpecFact),
}

impl fmt::Display for AndFactOrSpecFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AndFactOrSpecFact::AndFact(and_fact) => write!(f, "{}", and_fact),
            AndFactOrSpecFact::SpecFact(spec_fact) => write!(f, "{}", spec_fact),
        }
    }
}

impl AndFactOrSpecFact {
    pub fn line(&self) -> u32 {
        match self {
            AndFactOrSpecFact::AndFact(and_fact) => and_fact.line(),
            AndFactOrSpecFact::SpecFact(spec_fact) => spec_fact.line(),
        }
    }

    pub fn file_index(&self) -> usize {
        match self {
            AndFactOrSpecFact::AndFact(and_fact) => and_fact.file_index(),
            AndFactOrSpecFact::SpecFact(spec_fact) => spec_fact.file_index(),
        }
    }
}

impl AndFactOrSpecFact {
    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line(), self.file_index());
    }
}