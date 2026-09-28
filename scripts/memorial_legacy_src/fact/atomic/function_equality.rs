//! Function equality fact payloads.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct FnEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

impl FnEqualFact {
    #[cfg(test)]
    #[deprecated(note = "production facts must be created through Runtime::new_*_fact")]
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        FnEqualFact {
            fact_id: FactId::fresh(),
            left,
            right,
            line_file,
        }
    }
}

impl fmt::Display for FnEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}({}, {})", FACT_PREFIX, FN_EQ, self.left, self.right)
    }
}
