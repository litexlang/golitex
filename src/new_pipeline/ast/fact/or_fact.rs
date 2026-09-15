use super::{AndFact, AtomicFact, ChainFact};
use super::super::line_file::LineFile;
use crate::new_pipeline::runtime::FactId;

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
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuantifierFreeFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
}
