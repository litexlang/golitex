use std::fmt;
use crate::helper::str_with_line_file;
use crate::or_fact::OrFact;
use crate::forall_fact::ForallFact;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::and_fact::AndFact;
use crate::specific_fact::SpecFact;
pub enum Fact {
    SpecFact(SpecFact),
    OrFact(OrFact),
    AndFact(AndFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fact::SpecFact(spec_fact) => write!(f, "{}", spec_fact),
            Fact::OrFact(or_fact) => write!(f, "{}", or_fact),
            Fact::AndFact(and_fact) => write!(f, "{}", and_fact),
            Fact::ForallFact(forall_fact) => write!(f, "{}", forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => write!(f, "{}", forall_fact_with_iff),
        }
    }
}

impl Fact {
    pub fn line(&self) -> u32 {
        match self {
            Fact::SpecFact(spec_fact) => spec_fact.line(),
            Fact::OrFact(or_fact) => or_fact.line(),
            Fact::AndFact(and_fact) => and_fact.line(),
            Fact::ForallFact(forall_fact) => forall_fact.line(),
            Fact::ForallFactWithIff(forall_fact_with_iff) => forall_fact_with_iff.line(),
        }
    }

    pub fn file_index(&self) -> usize {
        match self {
            Fact::SpecFact(spec_fact) => spec_fact.file_index(),
            Fact::OrFact(or_fact) => or_fact.file_index(),
            Fact::AndFact(and_fact) => and_fact.file_index(),
            Fact::ForallFact(forall_fact) => forall_fact.file_index(),
            Fact::ForallFactWithIff(forall_fact_with_iff) => forall_fact_with_iff.file_index(),
        }
    }

    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line(), self.file_index());
    }
}