//! Positive and negative object equality facts.

use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub struct EqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

impl EqualFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        EqualFact {
            fact_id: FactId::fresh(),
            left,
            right,
            line_file,
        }
    }

    /// Builds an owned equality goal at a proof boundary from borrowed objects.
    /// Equality verifiers should receive the resulting `EqualFact`, rather than
    /// carrying `left`, `right`, and `line_file` as independent parameters.
    #[cfg(test)]
    pub fn new_from_refs(left: &Obj, right: &Obj, line_file: LineFile) -> Self {
        Self::new(left.clone(), right.clone(), line_file)
    }
}

impl NotEqualFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotEqualFact {
            fact_id: FactId::fresh(),
            left,
            right,
            line_file,
        }
    }
}

impl fmt::Display for EqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, EQUAL, self.right)
    }
}

impl fmt::Display for NotEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, NOT_EQUAL, self.right)
    }
}
