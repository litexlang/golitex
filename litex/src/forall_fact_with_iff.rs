use std::fmt;
use crate::consts::{EQUIVALENT_SIGN, COLON};
use crate::helper::{add_four_spaces_to_str_at_beginning, add_four_spaces_to_vec_at_beginning, str_with_line_file};
use crate::forall_fact::ForallFact;
use crate::specific_fact::SpecFact;

pub struct ForallFactWithIff {
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<SpecFact>,
    pub line: u32,
    pub file_index: usize,
}

impl ForallFactWithIff {
    pub fn new(forall_fact: ForallFact, iff_facts: Vec<SpecFact>, line: u32, file_index: usize) -> Self {
        ForallFactWithIff { forall_fact, iff_facts, line, file_index }
    }

    pub fn line(&self) -> u32 {
        self.line
    }

    pub fn file_index(&self) -> usize {
        self.file_index
    }

    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line(), self.file_index());
    }
}

impl fmt::Display for ForallFactWithIff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}{}\n{}", self.forall_fact, add_four_spaces_to_str_at_beginning(&EQUIVALENT_SIGN, 1), COLON, add_four_spaces_to_vec_at_beginning(&self.iff_facts, 2))
    }
}