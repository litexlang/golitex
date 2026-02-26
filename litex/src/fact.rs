use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;
use crate::or_fact::OrFact;
use crate::forall_fact::ForallFact;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::chain_fact::ChainFact;

pub enum Fact {
    AtomicFact(Box<AtomicFact>),
    ExistFact(Box<ExistFact>),
    OrFact(OrFact),
    ForallFact(ForallFact),
    ChainFact(ChainFact),
    ForallFactWithIff(ForallFactWithIff),
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            Fact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
            Fact::OrFact(or_fact) => write!(f, "{}", or_fact),
            Fact::ForallFact(forall_fact) => write!(f, "{}", forall_fact),
            Fact::ChainFact(chain_fact) => write!(f, "{}", chain_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => write!(f, "{}", forall_fact_with_iff),
        }
    }
}