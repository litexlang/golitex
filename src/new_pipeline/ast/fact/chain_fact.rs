use super::{AtomicFact, Fact};
use super::super::line_file::SourceLine;
use super::super::names::AtomicName;
use super::super::obj::Obj;
use crate::new_pipeline::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainFact {
    pub fact_id: FactId,
    pub objs: Vec<Obj>,
    pub prop_names: Vec<AtomicName>,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainAtomicFact {
    AtomicFact(AtomicFact),
    ChainFact(ChainFact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumericOrderChainClosureStep {
    pub start_object_index: usize,
    pub end_object_index: usize,
    pub premises: Vec<Fact>,
    pub conclusion: AtomicFact,
}
