use std::fmt;
use super::Stmt;
use crate::helper::vec_to_string_add_four_spaces_at_beginning_of_each_line;

pub struct ProveStmt {
    pub proof: Vec<Stmt>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ProveStmt {
    pub fn new(proof: Vec<Stmt>, line_file_index: Option<(usize, usize)>) -> Self {
        ProveStmt { proof, line_file_index }
    }
}

impl fmt::Display for ProveStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1))
    }
}