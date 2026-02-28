use crate::and_fact::AndFact;
use crate::specific_fact::SpecFact;
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

