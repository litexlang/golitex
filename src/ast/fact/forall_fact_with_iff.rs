use super::super::line_file::SourceLine;
use super::{ExistOrAndChainAtomicFact, ForallFact};
use crate::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallFactWithIff {
    pub fact_id: FactId,
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: Option<SourceLine>,
}
