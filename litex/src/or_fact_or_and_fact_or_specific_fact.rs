use crate::or_fact::OrFact;
use crate::and_fact::AndFact;
use crate::specific_fact::SpecFact;
use std::fmt;

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
    pub fn key(&self) -> String {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => or_fact.key(),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => and_fact.key(),
            OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => spec_fact.key(),
        }
    }
}

