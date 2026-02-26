use crate::specific_fact::SpecFact;

pub struct OrFact {
    pub facts: Vec<Box<SpecFact>>,
    pub line: u32,
}

impl OrFact {
    pub fn new(facts: Vec<Box<SpecFact>>, line: u32) -> Self {
        OrFact { facts, line }
    }
}