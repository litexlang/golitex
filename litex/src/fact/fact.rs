use std::fmt;
use super::or_fact::OrFact;
use super::forall_fact::ForallFact;
use super::forall_fact_with_iff::ForallFactWithIff;
use super::atomic_fact::AtomicFact;
use super::exist_fact::ExistFact;
use super::matchable_fact_with_atomic_fact_inside::AndFact;
use super::matchable_fact_with_atomic_fact_inside::ChainFact;
#[derive(Clone)]
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
    OrFact(OrFact),
    AndAtomicFact(AndFact),
    ChainAtomicFact(ChainFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            Fact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
            Fact::OrFact(or_fact) => write!(f, "{}", or_fact),
            Fact::AndAtomicFact(and_fact) => write!(f, "{}", and_fact),
            Fact::ChainAtomicFact(chain_fact) => write!(f, "{}", chain_fact),
            Fact::ForallFact(forall_fact) => write!(f, "{}", forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => write!(f, "{}", forall_fact_with_iff),
        }
    }
}

impl Fact {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            Fact::AtomicFact(a) => super::atomic_fact::line_file(a),
            Fact::ExistFact(e) => super::exist_fact::line_file(e),
            Fact::OrFact(o) => o.line_file_index,
            Fact::AndAtomicFact(a) => a.line_file_index(),
            Fact::ChainAtomicFact(c) => c.line_file_index(),
            Fact::ForallFact(f) => f.line_file_index,
            Fact::ForallFactWithIff(f) => f.line_file_index,
        }
    }
}