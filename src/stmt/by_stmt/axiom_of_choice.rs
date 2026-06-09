use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByAxiomOfChoiceStmt {
    pub family: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByAxiomOfChoiceStmt {
    pub fn new(family: Obj, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByAxiomOfChoiceStmt {
            family,
            proof,
            line_file,
        }
    }
}

impl fmt::Display for ByAxiomOfChoiceStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.proof.is_empty() {
            return write!(
                f,
                "{} {}{} {} {}",
                BY, AXIOM_OF_CHOICE, COLON, SET, self.family
            );
        }
        write!(
            f,
            "{} {}{} {} {}{}",
            BY, AXIOM_OF_CHOICE, COLON, SET, self.family, COLON
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
