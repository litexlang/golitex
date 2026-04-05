use crate::prelude::*;
use std::fmt;

/// Prove by contradiction (`by contra:`).
#[derive(Clone)]
pub struct ByContraStmt {
    pub to_prove: AtomicFact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: AtomicFact,
    pub line_file: LineFile,
}

impl ByContraStmt {
    pub fn new(
        to_prove: AtomicFact,
        proof: Vec<Stmt>,
        impossible_fact: AtomicFact,
        line_file: LineFile,
    ) -> Self {
        ByContraStmt {
            to_prove,
            proof,
            impossible_fact,
            line_file,
        }
    }
}

impl fmt::Display for ByContraStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}\n{}{}\n{}",
            BY,
            CONTRA,
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            add_four_spaces_at_beginning(self.to_prove.to_string(), 2),
        )?;
        if !self.proof.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1),
            )?;
        }
        write!(
            f,
            "\n{} {}",
            add_four_spaces_at_beginning(IMPOSSIBLE.to_string(), 1),
            &self.impossible_fact.to_string()
        )
    }
}
