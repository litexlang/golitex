use std::fmt;
use crate::consts::{CLAIM, COLON, PROVE};
use crate::fact::Fact;
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line,  vec_to_string_add_four_spaces_at_beginning_of_each_line, add_four_spaces_at_beginning};
use crate::stmt::Stmt;

pub struct ClaimProveStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}

impl ClaimProveStmt {
    pub fn new(to_prove: Fact, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ClaimProveStmt { to_prove, proof, line, file_index }
    }
}

impl fmt::Display for ClaimProveStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}", CLAIM, COLON,to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

