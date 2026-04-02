use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ProveStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ProveStmt {
    pub fn new(proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ProveStmt { proof, line_file }
    }
}

impl fmt::Display for ProveStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
        )
    }
}
