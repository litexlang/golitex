use std::fmt;
use super::atomic_fact::AtomicFact;
use super::matchable_fact_with_atomic_fact_inside::AndFact;
use super::matchable_fact_with_atomic_fact_inside::ChainFact;
use super::or_fact::OrFact;
use super::exist_fact::ExistFact;
use super::fact::Fact;

#[derive(Clone)]
pub enum ExistOrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
    ExistFact(ExistFact),
}

impl fmt::Display for ExistOrAndChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            ExistOrAndChainAtomicFact::AndFact(and_fact) => write!(f, "{}", and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => write!(f, "{}", chain_fact),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => write!(f, "{}", or_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
        }
    }
}

impl ExistOrAndChainAtomicFact {
    pub fn to_fact(self) -> Fact {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => Fact::AtomicFact(atomic_fact),
            ExistOrAndChainAtomicFact::AndFact(and_fact) => Fact::AndFact(and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => Fact::ChainFact(chain_fact),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => Fact::OrFact(or_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => Fact::ExistFact(exist_fact),
        }
    }
}