use crate::prelude::*;
use std::fmt;

#[derive(Clone, PartialEq)]
pub enum DefThmKind {
    Theorem,
    Axiom,
}

#[derive(Clone)]
pub struct DefThmStmt {
    pub kind: DefThmKind,
    pub names: Vec<String>,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

impl DefThmStmt {
    pub fn new(
        names: Vec<String>,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        DefThmStmt {
            kind: DefThmKind::Theorem,
            names,
            forall_fact,
            prove_process,
            line_file,
        }
    }

    pub fn new_axiom(names: Vec<String>, forall_fact: ForallFact, line_file: LineFile) -> Self {
        DefThmStmt {
            kind: DefThmKind::Axiom,
            names,
            forall_fact,
            prove_process: Vec::new(),
            line_file,
        }
    }

    pub fn is_axiom(&self) -> bool {
        self.kind == DefThmKind::Axiom
    }

    pub fn keyword(&self) -> &'static str {
        match self.kind {
            DefThmKind::Theorem => THM,
            DefThmKind::Axiom => AXIOM,
        }
    }

    pub fn store_reason(&self) -> &'static str {
        match self.kind {
            DefThmKind::Theorem => "proved theorem",
            DefThmKind::Axiom => "declared axiom",
        }
    }

    pub fn strict_mode_rejection_message() -> &'static str {
        "strict mode rejects user axiom statements; use thm/prove or move trusted background into an imported module"
    }

    pub fn output_type_string_for_stmt(&self) -> String {
        match self.kind {
            DefThmKind::Theorem => "theorem".to_string(),
            DefThmKind::Axiom => "axiom".to_string(),
        }
    }
}

impl fmt::Display for DefThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_axiom() {
            write!(
                f,
                "{} {}{}\n{}",
                self.keyword(),
                vec_to_string_with_sep(&self.names, ", ".to_string()),
                COLON,
                to_string_and_add_four_spaces_at_beginning_of_each_line(
                    &format!("{} {}", QUESTION_GOAL, self.forall_fact),
                    1
                )
            )?;
            return Ok(());
        }

        write!(
            f,
            "{} {}{}\n{}{}\n{}",
            self.keyword(),
            vec_to_string_with_sep(&self.names, ", ".to_string()),
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &self.forall_fact.to_string(),
                2
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
