use super::AtomicFact;
use super::super::line_file::SourceLine;
use crate::new_pipeline::runtime::FactId;

// Flat and of atomics only. No forall / exist / nested and: keeps store and
// known-atomic projection simple; name a universal as a prop if needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndFact {
    pub fact_id: FactId,
    pub facts: Vec<AtomicFact>,
    pub line_file: Option<SourceLine>,
}
