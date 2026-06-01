use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByZornLemmaStmt {
    pub set: Obj,
    pub prop_name: AtomicName,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByZornLemmaStmt {
    pub fn new(set: Obj, prop_name: AtomicName, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByZornLemmaStmt {
            set,
            prop_name,
            proof,
            line_file,
        }
    }
}

impl fmt::Display for ByZornLemmaStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {}{}",
            BY, ZORN_LEMMA, self.set, FROM, self.prop_name, COLON
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
