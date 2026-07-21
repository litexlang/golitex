use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct SketchStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl SketchStmt {
    pub fn new(proof: Vec<Stmt>, line_file: LineFile) -> Self {
        SketchStmt { proof, line_file }
    }
}

impl fmt::Display for SketchStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}\n{}",
            SKETCH,
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
        )
    }
}
