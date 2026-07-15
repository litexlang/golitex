use crate::prelude::*;
use std::fmt;

/// Prove a property of every finite set by its empty case and one fresh-element insertion.
#[derive(Clone)]
pub struct ByFiniteSetInducStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub param: String,
    pub element_param: String,
    pub smaller_set_param: String,
    pub base_proof: Vec<Stmt>,
    pub step_proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByFiniteSetInducStmt {
    pub fn new(
        to_prove: Vec<ExistOrAndChainAtomicFact>,
        param: String,
        element_param: String,
        smaller_set_param: String,
        base_proof: Vec<Stmt>,
        step_proof: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        ByFiniteSetInducStmt {
            to_prove,
            param,
            element_param,
            smaller_set_param,
            base_proof,
            step_proof,
            line_file,
        }
    }
}

impl fmt::Display for ByFiniteSetInducStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let question_goals = self
            .to_prove
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact))
            .collect::<Vec<String>>();
        write!(
            f,
            "{} {} {}:\n{}\n{} {} {} {} {}:\n{}\n{} {} {}, {}:\n{}",
            BY,
            INDUC,
            self.param,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&question_goals, 1),
            add_four_spaces_at_beginning(QUESTION_GOAL.to_string(), 1),
            FROM,
            self.param,
            EQUAL,
            "{}",
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.base_proof, 2),
            add_four_spaces_at_beginning(QUESTION_GOAL.to_string(), 1),
            INDUC,
            self.element_param,
            self.smaller_set_param,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.step_proof, 2),
        )
    }
}
