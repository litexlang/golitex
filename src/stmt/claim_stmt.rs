use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ClaimStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ClaimStmt {
    pub fn new(fact: Fact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ClaimStmt {
            fact,
            proof,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "proved claim"
    }
}

impl fmt::Display for ClaimStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}\n{}\n{}",
            CLAIM,
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &format!("{} {}", QUESTION_GOAL, self.fact),
                1,
            ),
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
        )
    }
}
