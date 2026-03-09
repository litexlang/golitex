use std::fmt;
use super::or_fact::OrFact;
use super::forall_fact::ForallFact;
use super::forall_fact_with_iff::ForallFactWithIff;
use super::and_fact::AndFact;
use super::atomic_fact::AtomicFact;
use super::exist_fact::ExistFact;
#[derive(Clone)]
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
    OrFact(OrFact),
    AndFact(AndFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            Fact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
            Fact::OrFact(or_fact) => write!(f, "{}", or_fact),
            Fact::AndFact(and_fact) => write!(f, "{}", and_fact),
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
            Fact::AndFact(a) => a.line_file(),
            Fact::ForallFact(f) => f.line_file_index,
            Fact::ForallFactWithIff(f) => f.line_file_index,
        }
    }
}