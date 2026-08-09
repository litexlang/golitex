use crate::prelude::*;
use std::fmt;

/// Prove a property of every finite set by its empty case and one fresh-element insertion.
#[derive(Clone)]
pub struct ByFiniteSetInducStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub param: String,
    pub param_binding: SymbolBinding,
    pub carrier_set: Option<Obj>,
    pub element_param: String,
    pub element_param_binding: SymbolBinding,
    pub smaller_set_param: String,
    pub smaller_set_param_binding: SymbolBinding,
    pub base_proof: Vec<Stmt>,
    pub step_proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByFiniteSetInducStmt {
    pub fn new(
        to_prove: Vec<ExistOrAndChainAtomicFact>,
        param: String,
        param_binding: SymbolBinding,
        carrier_set: Option<Obj>,
        element_param: String,
        element_param_binding: SymbolBinding,
        smaller_set_param: String,
        smaller_set_param_binding: SymbolBinding,
        base_proof: Vec<Stmt>,
        step_proof: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        ByFiniteSetInducStmt {
            to_prove,
            param,
            param_binding,
            carrier_set,
            element_param,
            element_param_binding,
            smaller_set_param,
            smaller_set_param_binding,
            base_proof,
            step_proof,
            line_file,
        }
    }
}

impl fmt::Display for ByFiniteSetInducStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let question_goals = self
            .to_prove
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact))
            .collect::<Vec<String>>();
        write!(f, "{} {} {}", BY, INDUC, self.param)?;
        if let Some(carrier_set) = &self.carrier_set {
            write!(f, " {} {}", IN, carrier_set)?;
        }
        write!(
            f,
            ":\n{}",
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&question_goals, 1),
        )?;

        let base_colon = if self.base_proof.is_empty() {
            ""
        } else {
            COLON
        };
        write!(
            f,
            "\n{}",
            add_four_spaces_at_beginning(
                format!(
                    "{} {} {} {} {}{}",
                    QUESTION_GOAL, FROM, self.param, EQUAL, "{}", base_colon
                ),
                1,
            ),
        )?;
        if !self.base_proof.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.base_proof, 2),
            )?;
        }

        let step_colon = if self.step_proof.is_empty() {
            ""
        } else {
            COLON
        };
        write!(
            f,
            "\n{}",
            add_four_spaces_at_beginning(
                format!(
                    "{} {} {}, {}{}",
                    QUESTION_GOAL, INDUC, self.element_param, self.smaller_set_param, step_colon
                ),
                1,
            ),
        )?;
        if !self.step_proof.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.step_proof, 2),
            )?;
        }
        Ok(())
    }
}
