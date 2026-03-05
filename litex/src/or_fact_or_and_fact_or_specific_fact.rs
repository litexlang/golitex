use crate::or_fact::OrFact;
use crate::and_fact::AndFact;
use crate::specific_fact::SpecFact;
use crate::fact::Fact;
use std::fmt;

#[derive(Clone)]
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

    pub fn to_fact(self) -> Fact {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => Fact::OrFact(or_fact),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => Fact::AndFact(and_fact),
            OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => match spec_fact {
                SpecFact::AtomicFact(atomic_fact) => Fact::AtomicFact(atomic_fact),
                SpecFact::ExistFact(exist_fact) => Fact::ExistFact(exist_fact),
            },
        }
    }
}

