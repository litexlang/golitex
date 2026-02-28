use std::fmt;
use crate::stmt::Stmt;
use crate::helper::vec_to_string_add_four_spaces_at_beginning_of_each_line;

pub struct ProveStmt {
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}

impl ProveStmt {
    pub fn new(proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ProveStmt { proof, line, file_index }
    }
}

impl fmt::Display for ProveStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1))
    }
}