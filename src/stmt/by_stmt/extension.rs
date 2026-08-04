use crate::prelude::*;
use std::fmt;

/// Prove set equality by extensionality (`by extension:` with a `?` equality goal).
#[derive(Clone)]
pub struct ByExtensionStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for ByExtensionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}\n{}",
            BY,
            EXTENSION,
            COLON,
            add_four_spaces_at_beginning(
                format!("{} {} {} {}", QUESTION_GOAL, self.left, EQUAL, self.right),
                1,
            )
        )?;
        if !self.proof.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
            )?;
        }
        Ok(())
    }
}

impl ByExtensionStmt {
    pub fn new(left: Obj, right: Obj, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByExtensionStmt {
            left,
            right,
            proof,
            line_file,
        }
    }
}
