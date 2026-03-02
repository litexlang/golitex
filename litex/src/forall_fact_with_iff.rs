use std::fmt;
use crate::consts::{EQUIVALENT_SIGN, COLON};
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_add_four_spaces_at_beginning_of_each_line};
use crate::forall_fact::ForallFact;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;

pub struct ForallFactWithIff {
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line: u32,
    pub file_index: usize,
}

impl ForallFactWithIff {
    pub fn new(forall_fact: ForallFact, iff_facts: Vec<OrFactOrAndFactOrSpecFact>, line: u32, file_index: usize) -> Self {
        ForallFactWithIff { forall_fact, iff_facts, line, file_index }
    }
}

impl fmt::Display for ForallFactWithIff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}{}\n{}", self.forall_fact, to_string_and_add_four_spaces_at_beginning_of_each_line(&EQUIVALENT_SIGN, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.iff_facts, 2))
    }
}