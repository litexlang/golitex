//! Negated universal fact payload.

use crate::prelude::*;

#[derive(Clone)]
pub struct NotForallFact {
    pub fact_id: FactId,
    pub forall_fact: ForallFact,
}

impl NotForallFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(forall_fact: ForallFact) -> Self {
        Self {
            fact_id: FactId::fresh(),
            forall_fact,
        }
    }

    pub fn line_file(&self) -> LineFile {
        self.forall_fact.line_file.clone()
    }
}
