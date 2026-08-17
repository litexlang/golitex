use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByThmStmt {
    pub name: AtomicName,
    pub args: Vec<Obj>,
    pub selected_facts: Option<Vec<Fact>>,
    pub line_file: LineFile,
}

impl ByThmStmt {
    pub fn new(
        name: AtomicName,
        args: Vec<Obj>,
        selected_facts: Option<Vec<Fact>>,
        line_file: LineFile,
    ) -> Self {
        ByThmStmt {
            name,
            args,
            selected_facts,
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
        if let Some(selected_facts) = self.selected_facts.as_ref() {
            let question_goals = selected_facts
                .iter()
                .map(|fact| format!("{} {}", QUESTION_GOAL, fact))
                .collect::<Vec<String>>();
            if question_goals.len() == 1 {
                write!(f, " {} {}", RIGHT_ARROW, selected_facts[0])?;
            } else {
                write!(
                    f,
                    "{}\n{}",
                    COLON,
                    vec_to_string_add_four_spaces_at_beginning_of_each_line(&question_goals, 1)
                )?;
            }
        }
        Ok(())
    }
}
