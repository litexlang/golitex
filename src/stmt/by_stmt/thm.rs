use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByThmStmt {
    pub name: AtomicName,
    pub args: Vec<Obj>,
    pub selected_fact: Option<AtomicFact>,
    pub line_file: LineFile,
}

impl ByThmStmt {
    pub fn new(
        name: AtomicName,
        args: Vec<Obj>,
        selected_fact: Option<AtomicFact>,
        line_file: LineFile,
    ) -> Self {
        ByThmStmt {
            name,
            args,
            selected_fact,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "theorem instantiation"
    }

    pub fn selected_fact_store_reason() -> &'static str {
        "selected theorem consequence"
    }
}

impl fmt::Display for ByThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {}{}",
            BY,
            THM,
            self.name,
            braced_vec_to_string(&self.args)
        )?;
        if let Some(selected_fact) = self.selected_fact.as_ref() {
            write!(f, " {} {}", RIGHT_ARROW, selected_fact)?;
        }
        Ok(())
    }
}
