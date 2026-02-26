use std::fmt;
use crate::consts::{RIGHT_ARROW, COLON};
use crate::helper::{add_four_spaces_to_str_at_beginning, add_four_spaces_to_vec_at_beginning};
use crate::forall_fact::ForallFact;
use crate::specific_fact::SpecFact;

pub struct ForallFactWithIff {
    pub forall_fact: Box<ForallFact>,
    pub iff_facts: Vec<Box<SpecFact>>,
    pub line: u32,
}

impl ForallFactWithIff {
    pub fn new(forall_fact: Box<ForallFact>, iff_facts: Vec<Box<SpecFact>>, line: u32) -> Self {
        ForallFactWithIff { forall_fact, iff_facts, line }
    }

    pub fn line(&self) -> u32 {
        self.line
    }
}

impl fmt::Display for ForallFactWithIff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}{}\n{}", self.forall_fact, add_four_spaces_to_str_at_beginning(&RIGHT_ARROW, 1), COLON, add_four_spaces_to_vec_at_beginning(&self.iff_facts, 2))
    }
}