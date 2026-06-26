use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByRegularityAxiomStmt {
    pub set: Obj,
    pub line_file: LineFile,
}

impl ByRegularityAxiomStmt {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        ByRegularityAxiomStmt { set, line_file }
    }
}

impl fmt::Display for ByRegularityAxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}({})", BY, REGULARITY_AXIOM, self.set)
    }
}
