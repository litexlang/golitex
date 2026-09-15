use super::QuantifierFreeFact;
use super::super::line_file::LineFile;
use super::super::param::TypedParameterList;
use crate::new_pipeline::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExistFact {
    PlainExistFact(PlainExistFact),
    ExistUniqueFact(PlainExistFact),
    NotExistFact(PlainExistFact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlainExistFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: Option<LineFile>,
}
