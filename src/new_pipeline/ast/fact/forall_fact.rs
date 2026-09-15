use super::{AndFact, AtomicFact, ChainFact, ExistFact, Fact, OrFact};
use super::super::line_file::LineFile;
use super::super::param::TypedParameterList;
use crate::new_pipeline::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExistOrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
    ExistFact(ExistFact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub dom_facts: Vec<Fact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: Option<LineFile>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForallConclusionLocation {
    DirectThenFact(DirectForallConclusionLocation),
    AndFactComponent(AndFactComponentForallConclusionLocation),
    ChainFactComponent(ChainFactComponentForallConclusionLocation),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirectForallConclusionLocation {
    pub then_fact_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndFactComponentForallConclusionLocation {
    pub then_fact_index: usize,
    pub component_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainFactComponentForallConclusionLocation {
    pub then_fact_index: usize,
    pub component_index: usize,
}
