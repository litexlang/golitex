use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ForallFact {
    pub params_def_with_type: ParamDefWithType,
    pub dom_facts: Vec<ExistOrAndChainAtomicFact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: LineFile,
}

impl ForallFact {
    pub fn new(
        params_def_with_type: ParamDefWithType,
        dom_facts: Vec<ExistOrAndChainAtomicFact>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Self {
        ForallFact {
            params_def_with_type,
            dom_facts,
            then_facts,
            line_file,
        }
    }
}

impl fmt::Display for ForallFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.dom_facts.len() {
            0 => write!(
                f,
                "{} {}{}\n{}",
                FORALL,
                self.params_def_with_type.to_string(),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)
            ),
            _ => write!(
                f,
                "{} {}{}\n{}\n{}{}\n{}",
                FORALL,
                self.params_def_with_type.to_string(),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1),
                to_string_and_add_four_spaces_at_beginning_of_each_line(&RIGHT_ARROW, 1),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)
            ),
        }
    }
}
