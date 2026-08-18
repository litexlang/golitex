use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct AxiomStmt {
    pub name: String,
    pub forall_fact: ForallFact,
    pub line_file: LineFile,
}

impl AxiomStmt {
    pub fn new(name: String, forall_fact: ForallFact, line_file: LineFile) -> Self {
        AxiomStmt {
            name,
            forall_fact,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "declared axiom"
    }

    pub fn strict_mode_rejection_message() -> &'static str {
        "strict mode rejects user axiom statements; use thm with a `?` goal or move trusted background into an imported module"
    }
}

impl fmt::Display for AxiomStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}\n{}",
            AXIOM,
            self.name,
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &format!("{} {}", QUESTION_GOAL, self.forall_fact),
                1
            )
        )
    }
}
