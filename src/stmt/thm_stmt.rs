use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct DefThmStmt {
    pub name: String,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

impl DefThmStmt {
    pub fn new(
        name: String,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        DefThmStmt {
            name,
            forall_fact,
            prove_process,
            line_file,
        }
    }

    pub fn store_reason(&self) -> &'static str {
        "proved theorem"
    }
}

impl fmt::Display for DefThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}\n{}",
            THM,
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
