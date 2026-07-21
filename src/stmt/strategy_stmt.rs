use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct UseStrategyStmt {
    pub name: AtomicName,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct StopStrategyStmt {
    pub name: AtomicName,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefStrategyStmt {
    pub names: Vec<String>,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

impl UseStrategyStmt {
    pub fn new(name: AtomicName, line_file: LineFile) -> Self {
        UseStrategyStmt { name, line_file }
    }
}

impl fmt::Display for UseStrategyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", USE, STRATEGY, self.name)
    }
}

impl StopStrategyStmt {
    pub fn new(name: AtomicName, line_file: LineFile) -> Self {
        StopStrategyStmt { name, line_file }
    }
}

impl fmt::Display for StopStrategyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", STOP, STRATEGY, self.name)
    }
}

impl DefStrategyStmt {
    pub fn new(
        names: Vec<String>,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        DefStrategyStmt {
            names,
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
            vec_to_string_with_sep(&self.names, ", ".to_string()),
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
