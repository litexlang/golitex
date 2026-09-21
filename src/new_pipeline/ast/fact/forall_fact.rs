use super::{AndFact, AtomicFact, ChainFact, Fact, OrFact, PlainExistFact};
use super::super::line_file::LineFile;
use super::super::param::TypedParameterList;
use crate::new_pipeline::runtime::FactId;

// Forall then-clause shapes. Exist-family facts are allowed here; nested forall is not.
// Nested forall flattens like nested exist (`forall x: forall y:` → one forall
// with more binders / dom). Keeping then free of forall makes conclusion indexes
// (atomic / or / later exist) a single non-universal layer. Need a nested
// universal? Name it as a prop and conclude that atomic instead.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExistOrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
    ExistFact(PlainExistFact),
    ExistUniqueFact(PlainExistFact),
    NotExistFact(PlainExistFact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    // Left-to-right WD: each succeeds, then is assumed for later dom / then facts (temporary).
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
