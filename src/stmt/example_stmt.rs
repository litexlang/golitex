use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ExampleStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ExampleStmt {
    pub fn new(fact: Fact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ExampleStmt {
            fact,
            proof,
            line_file,
        }
    }
}

impl fmt::Display for ExampleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}\n{}\n{}",
            EXAMPLE,
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &format!("{} {}", QUESTION_GOAL, self.fact),
                1,
            ),
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
        )
    }
}
