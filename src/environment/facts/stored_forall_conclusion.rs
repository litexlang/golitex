//! Provenance of one indexed conclusion from a stored universal fact.

use crate::prelude::*;
use std::rc::Rc;

/// One conclusion indexed from one exact stored universal fact.
///
/// The complete source proposition and `FactId` remain together with the
/// structural conclusion location, so consumers never rebuild a smaller
/// universal from the matched conclusion.
pub struct StoredForallConclusionReference {
    pub params_def: TypedParameterList,
    pub dom: Vec<Fact>,
    pub line_file: LineFile,
    /// Exact stored universal that produced every indexed conclusion sharing
    /// this record. A consumer may select one conclusion for matching, but its
    /// proof citation must retain this complete source proposition and FactId.
    pub source_forall: Rc<ForallFact>,
    pub source_fact_id: FactId,
    pub conclusion_location: ForallConclusionLocation,
}

impl StoredForallConclusionReference {
    pub fn new(
        source_forall: Rc<ForallFact>,
        source_fact_id: FactId,
        conclusion_location: ForallConclusionLocation,
    ) -> Self {
        StoredForallConclusionReference {
            params_def: source_forall.typed_parameters.clone(),
            dom: source_forall.dom_facts.clone(),
            line_file: source_forall.line_file.clone(),
            source_forall,
            source_fact_id,
            conclusion_location,
        }
    }

    pub fn source_fact(&self) -> Fact {
        self.source_forall.as_ref().clone().into()
    }

    pub fn with_conclusion_location(
        &self,
        conclusion_location: ForallConclusionLocation,
    ) -> Rc<Self> {
        Rc::new(Self::new(
            self.source_forall.clone(),
            self.source_fact_id,
            conclusion_location,
        ))
    }
}
