use std::fmt;
use crate::keywords::{FORALL, COLON, RIGHT_ARROW};
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma};
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::parameter_type_and_property::ParamDefWithParamType;
pub struct ForallFact {
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub then_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ForallFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamType>,
        dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
        then_facts: Vec<OrFactOrAndFactOrSpecFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        ForallFact { params_def_with_type, dom_facts, then_facts, line_file_index }
    }
}

impl fmt::Display for ForallFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.dom_facts.len() {
            0 => write!(f, "{} {}{}\n{}", FORALL, vec_to_string_join_by_comma(&self.params_def_with_type),COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)),
            _ => write!(f, "{} {}{}\n{}\n{}{}\n{}", FORALL, vec_to_string_join_by_comma(&self.params_def_with_type),COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1), to_string_and_add_four_spaces_at_beginning_of_each_line(&RIGHT_ARROW, 1), COLON,vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)),
        }
    }
}
