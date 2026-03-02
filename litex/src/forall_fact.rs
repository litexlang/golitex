use std::fmt;
use crate::consts::{FORALL, COLON, RIGHT_ARROW};
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma};
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::parameter_type_and_property::ParameterTypeOrParameterProperty;
pub struct ForallFact {
    pub param_type_or_property_pairs: Vec<ParameterTypeOrParameterProperty>,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub then_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line: u32,
    pub file_index: usize,
}

impl ForallFact {
    pub fn new(
        param_type_or_property_pairs: Vec<ParameterTypeOrParameterProperty>,
        dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
        then_facts: Vec<OrFactOrAndFactOrSpecFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        ForallFact { param_type_or_property_pairs, dom_facts, then_facts, line, file_index }
    }
}

impl fmt::Display for ForallFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.dom_facts.len() {
            0 => write!(f, "{} {}{}\n{}", FORALL, vec_to_string_join_by_comma(&self.param_type_or_property_pairs),COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)),
            _ => write!(f, "{} {}{}\n{}\n{}{}\n{}", FORALL, vec_to_string_join_by_comma(&self.param_type_or_property_pairs),COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1), to_string_and_add_four_spaces_at_beginning_of_each_line(&RIGHT_ARROW, 1), COLON,vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)),
        }
    }
}
