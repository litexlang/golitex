use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct TrustStmt {
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

impl TrustStmt {
    pub fn new(facts: Vec<Fact>, line_file: LineFile) -> Self {
        TrustStmt { facts, line_file }
    }

    pub fn store_reason() -> &'static str {
        "unproved assumption"
    }

    pub fn strict_mode_rejection_message() -> &'static str {
        "strict mode rejects user trust statements; use claim/thm with a `?` goal or move trusted background into an imported module"
    }
}

impl fmt::Display for TrustStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.facts.len() == 1 {
            write!(f, "{} {}", TRUST, self.facts[0])
        } else {
            write!(
                f,
                "{}{}\n{}",
                TRUST,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1),
            )
        }
    }
}
