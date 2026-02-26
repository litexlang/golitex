use std::fmt;
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
}

impl fmt::Display for ForallFactWithIff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("ForallFactWithIff is not implemented");
    }
}