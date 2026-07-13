use crate::prelude::*;
use std::fmt;

/// List-set enumeration: `by enumerate finite_set:` then `?` / one `forall`.
#[derive(Clone)]
pub struct ByEnumerateFiniteSetStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByEnumerateFiniteSetStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByEnumerateFiniteSetStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        Ok(self.forall_fact.clone().into())
    }
}

impl fmt::Display for ByEnumerateFiniteSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}:\n{}",
            BY,
            ENUMERATE,
            FINITE_SET,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &format!("{} {}", QUESTION_GOAL, self.forall_fact),
                1
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
