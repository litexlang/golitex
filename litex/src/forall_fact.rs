use std::fmt;
use crate::consts::{FORALL, COLON, RIGHT_ARROW};
use crate::helper::{add_four_spaces_to_vec_at_beginning, add_four_spaces_to_str_at_beginning, vec_pair_to_string};
use crate::parameter_set::ParameterSet;
use crate::specific_fact::SpecFact;

pub struct ForallFact {
    pub params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub dom_facts: Vec<Box<SpecFact>>,
    pub then_facts: Vec<Box<SpecFact>>,
    pub line: u32,
}

impl ForallFact {
    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        dom_facts: Vec<Box<SpecFact>>,
        then_facts: Vec<Box<SpecFact>>,
        line: u32,
    ) -> Self {
        ForallFact { params, param_sets, dom_facts, then_facts, line }
    }

    pub fn line(&self) -> u32 {
        self.line
    }
}

impl fmt::Display for ForallFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.dom_facts.len() {
            0 => write!(f, "{} {}{}\n{}", FORALL, vec_pair_to_string(&self.params, &self.param_sets),COLON, add_four_spaces_to_vec_at_beginning(&self.then_facts, 1)),
            _ => write!(f, "{} {}{}\n{}\n{}{}\n{}", FORALL, vec_pair_to_string(&self.params, &self.param_sets),COLON, add_four_spaces_to_vec_at_beginning(&self.dom_facts, 1), add_four_spaces_to_str_at_beginning(&RIGHT_ARROW, 1), COLON,add_four_spaces_to_vec_at_beginning(&self.then_facts, 2)),
        }
    }
}
