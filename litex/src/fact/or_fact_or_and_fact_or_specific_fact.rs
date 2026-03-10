use super::or_fact::OrFact;
use super::matchable_fact_with_atomic_fact_inside::AndFact;
use super::atomic_fact::AtomicFact;
use super::fact::Fact;
use std::fmt;

#[derive(Clone)]
pub enum OrFactOrAndFactOrSpecFact {
    OrFact(OrFact),
    AndFact(AndFact),
    AtomicFact(AtomicFact)
}

impl fmt::Display for OrFactOrAndFactOrSpecFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => write!(f, "{}", or_fact),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => write!(f, "{}", and_fact),
            OrFactOrAndFactOrSpecFact::AtomicFact(spec_fact) => write!(f, "{}", spec_fact),
        }
    }
}

impl OrFactOrAndFactOrSpecFact {
    pub fn key(&self) -> String {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => or_fact.key(),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => and_fact.key(),
            OrFactOrAndFactOrSpecFact::AtomicFact(spec_fact) => spec_fact.key(),
        }
    }

    pub fn to_fact(self) -> Fact {
        match self {
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => Fact::OrFact(or_fact),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => Fact::AndAtomicFact(and_fact),
            OrFactOrAndFactOrSpecFact::AtomicFact(atomic_fact) => Fact::AtomicFact(atomic_fact),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fact::{AtomicFact, EqualFact};

    #[test]
    fn test_or_fact_or_and_fact_or_specific_fact_key() {
        let o = OrFactOrAndFactOrSpecFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact::new(crate::obj::Obj::mk("p"), crate::obj::Obj::mk("q"), Some((1, 0))),
        ));
        let _k = o.key();
    }
}

