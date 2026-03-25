use crate::common::helper::vec_to_string_add_four_spaces_at_beginning_of_each_line;
use crate::common::keywords::{COLON, KNOW};
use crate::fact::Fact;
use std::fmt;

#[derive(Clone)]
pub struct KnowStmt {
    pub facts: Vec<Fact>,
    pub line_file: (usize, usize),
}

impl KnowStmt {
    pub fn new(facts: Vec<Fact>, line_file: (usize, usize)) -> Self {
        KnowStmt { facts, line_file }
    }
}

impl fmt::Display for KnowStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.facts.len() == 1 {
            write!(f, "know {}", self.facts[0])
        } else {
            write!(
                f,
                "{}{}\n{}",
                KNOW,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1),
            )
        }
    }
}
