use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ScratchStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ScratchStmt {
    pub fn new(proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ScratchStmt { proof, line_file }
    }
}

impl fmt::Display for ScratchStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}\n{}",
            SCRATCH,
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
        )
    }
}
