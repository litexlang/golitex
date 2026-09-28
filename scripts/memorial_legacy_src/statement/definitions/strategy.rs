//! Strategy definition statement form.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct DefStrategyStmt {
    pub name: String,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

impl DefStrategyStmt {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        DefStrategyStmt {
            name,
            forall_fact,
            prove_process,
            line_file,
        }
    }
}

impl fmt::Display for DefStrategyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}\n{}",
            STRATEGY,
            self.name,
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &format!("{} {}", QUESTION_GOAL, self.forall_fact),
                1
            )
        )?;
        if !self.prove_process.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.prove_process, 1)
            )?;
        }
        Ok(())
    }
}
