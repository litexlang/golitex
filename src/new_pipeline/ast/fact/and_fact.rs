use super::AtomicFact;
use super::super::line_file::LineFile;
use crate::new_pipeline::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndFact {
    pub fact_id: FactId,
    pub facts: Vec<AtomicFact>,
    pub line_file: Option<LineFile>,
}
