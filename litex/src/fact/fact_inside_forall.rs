use std::fmt;
use super::atomic_fact::AtomicFact;
use super::matchable_fact_with_atomic_fact_inside::AndFact;
use super::matchable_fact_with_atomic_fact_inside::ChainFact;
use super::or_fact::OrFact;
use super::exist_fact::ExistFact;

#[derive(Clone)]
pub enum FactInsideForall {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
    ExistFact(ExistFact),
}

impl fmt::Display for FactInsideForall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FactInsideForall::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            FactInsideForall::AndFact(and_fact) => write!(f, "{}", and_fact),
            FactInsideForall::ChainFact(chain_fact) => write!(f, "{}", chain_fact),
            FactInsideForall::OrFact(or_fact) => write!(f, "{}", or_fact),
            FactInsideForall::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
        }
    }
}