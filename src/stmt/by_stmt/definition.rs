use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByDefStmt {
    pub fact: NormalAtomicFact,
    pub line_file: LineFile,
}

impl ByDefStmt {
    pub fn new(fact: NormalAtomicFact, line_file: LineFile) -> Self {
        ByDefStmt { fact, line_file }
    }

    pub fn store_reason() -> &'static str {
        "proof by definition"
    }
}

impl fmt::Display for ByDefStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", BY, DEF, self.fact)
    }
}
