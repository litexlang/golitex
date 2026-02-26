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

impl Fact {
    pub fn box_atomic_fact(fact: Box<AtomicFact>) -> Box<Fact> {
        Box::new(Fact::AtomicFact(fact))
    }
    pub fn box_exist_fact(fact: Box<ExistFact>) -> Box<Fact> {
        Box::new(Fact::ExistFact(fact))
    }
    pub fn box_or_fact(fact: OrFact) -> Box<Fact> {
        Box::new(Fact::OrFact(fact))
    }
    pub fn box_forall_fact(fact: ForallFact) -> Box<Fact> {
        Box::new(Fact::ForallFact(fact))
    }
    pub fn box_chain_fact(fact: ChainFact) -> Box<Fact> {
        Box::new(Fact::ChainFact(fact))
    }
    pub fn box_forall_fact_with_iff(fact: ForallFactWithIff) -> Box<Fact> {
        Box::new(Fact::ForallFactWithIff(fact))
    }
}

