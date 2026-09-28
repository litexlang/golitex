use super::{AndFact, AtomicFact, ChainFact};
use super::super::line_file::SourceLine;
use crate::runtime::FactId;

// Or branches are only atomic / flat and / chain (not nested or).
// Parser: and binds tighter than or, so each branch is one finished and-chain unit.
// Search: fixed branch shapes make matching a known or against a goal or easier.
// No forall (and no exist) inside or: index keys stay quantifier-free; wrap a
// needed universal as a named prop if you must mention it under or/and/exist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrFact {
    pub fact_id: FactId,
    pub facts: Vec<AndChainAtomicFact>,
    pub line_file: Option<SourceLine>,
}

// Quantifier-free clause grammar: atomic, and, chain, or.
// Used as exist / set-builder bodies (and similar). Deliberately excludes forall
// and nested exist so index keys and known-fact search stay shape-simple; nest
// exist by flattening binders, and name a forall as a prop when needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuantifierFreeFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
}
