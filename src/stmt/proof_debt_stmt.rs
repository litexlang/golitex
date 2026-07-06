use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ProofDebtStmt {
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

impl ProofDebtStmt {
    pub fn new(facts: Vec<Fact>, line_file: LineFile) -> Self {
        ProofDebtStmt { facts, line_file }
    }

    pub fn store_reason() -> &'static str {
        "warning: unproved proof_debt assumption"
    }

    pub fn strict_mode_rejection_message() -> &'static str {
        "strict mode rejects user proof_debt statements; use claim/thm/prove or move trusted background into an imported module"
    }
}

impl fmt::Display for ProofDebtStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.facts.len() == 1 {
            write!(f, "proof_debt {}", self.facts[0])
        } else {
            write!(
                f,
                "{}{}\n{}",
                PROOF_DEBT,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1),
            )
        }
    }
}
