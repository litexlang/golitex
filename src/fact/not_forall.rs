//! Negated universal fact payload.

use crate::prelude::*;

#[derive(Clone)]
pub struct NotForallFact {
    pub forall_fact: ForallFact,
}

impl NotForallFact {
    pub fn new(forall_fact: ForallFact) -> Self {
        Self { forall_fact }
    }

    pub fn line_file(&self) -> LineFile {
        self.forall_fact.line_file.clone()
    }
}
