use std::fmt;
use crate::consts::{FORALL, COLON, RIGHT_ARROW};
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_str_add_four_spaces_at_beginning_of_each_line, vec_pair_to_string};
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::parameter_type::ParameterType;

pub struct ForallFact {
    pub params: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub then_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line: u32,
    pub file_index: usize,
}

impl ForallFact {
    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ParameterType>,
        dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
        then_facts: Vec<OrFactOrAndFactOrSpecFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        ForallFact { params, param_types: param_sets, dom_facts, then_facts, line, file_index }
    }
}

impl fmt::Display for ForallFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.dom_facts.len() {
            0 => write!(f, "{} {}{}\n{}", FORALL, vec_pair_to_string(&self.params, &self.param_types),COLON, vec_to_str_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)),
            _ => write!(f, "{} {}{}\n{}\n{}{}\n{}", FORALL, vec_pair_to_string(&self.params, &self.param_types),COLON, vec_to_str_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1), to_string_and_add_four_spaces_at_beginning_of_each_line(&RIGHT_ARROW, 1), COLON,vec_to_str_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)),
        }
    }
}
