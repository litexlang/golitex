use crate::specific_fact::SpecFact;
use std::fmt;
use crate::consts::AND;

pub struct AndFact {
    pub facts: Vec<SpecFact>,
    pub line: u32,
    pub file_index: usize,
}

impl AndFact {
    pub fn new(facts: Vec<SpecFact>, line: u32, file_index: usize) -> Self {
        AndFact { facts, line, file_index }
    }
}

impl fmt::Display for AndFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // join by " and "
        write!(f, "{}", self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>().join(format!(" {} ", AND).as_str()))
    }
}