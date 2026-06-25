use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct DefThmStmt {
    pub names: Vec<String>,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub kind: DefThmKind,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub enum DefThmKind {
    Thm,
    Lemma,
}

impl DefThmStmt {
    pub fn new(
        names: Vec<String>,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        kind: DefThmKind,
        line_file: LineFile,
    ) -> Self {
        DefThmStmt {
            names,
            forall_fact,
            prove_process,
            kind,
            line_file,
        }
    }

    pub fn new_thm(
        names: Vec<String>,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        Self::new(
            names,
            forall_fact,
            prove_process,
            DefThmKind::Thm,
            line_file,
        )
    }

    pub fn new_lemma(
        names: Vec<String>,
        forall_fact: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        Self::new(
            names,
            forall_fact,
            prove_process,
            DefThmKind::Lemma,
            line_file,
        )
    }

    pub fn stores_forall_fact(&self) -> bool {
        matches!(self.kind, DefThmKind::Lemma)
    }

    pub fn keyword(&self) -> &'static str {
        match self.kind {
            DefThmKind::Thm => THM,
            DefThmKind::Lemma => LEMMA,
        }
    }

    pub fn store_reason() -> &'static str {
        "proved lemma"
    }

    pub fn output_type_string_for_stmt(&self) -> String {
        match self.kind {
            DefThmKind::Thm => "theorem".to_string(),
            DefThmKind::Lemma => "lemma".to_string(),
        }
    }
}

impl fmt::Display for DefThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
