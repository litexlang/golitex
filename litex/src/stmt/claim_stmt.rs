use std::fmt;
use crate::fact::Fact;
use crate::common::keywords::{CLAIM, COLON, PROVE};
use crate::common::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_add_four_spaces_at_beginning_of_each_line, add_four_spaces_at_beginning};
use super::Stmt;

pub struct ClaimStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ClaimStmt {
    pub fn new(fact: Fact, proof: Vec<Stmt>, line_file_index: Option<(usize, usize)>) -> Self {
        ClaimStmt { fact, proof, line_file_index }
    }

    pub fn line_file(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

impl fmt::Display for ClaimStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}", CLAIM, COLON, to_string_and_add_four_spaces_at_beginning_of_each_line(&self.fact.to_string(), 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}
