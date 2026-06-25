use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct TryStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl TryStmt {
    pub fn new(proof: Vec<Stmt>, line_file: LineFile) -> Self {
        TryStmt { proof, line_file }
    }
}

impl fmt::Display for TryStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}\n{}",
            TRY,
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
        )
    }
}
