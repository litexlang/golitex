use std::fmt;
use crate::fact::Fact;

pub struct KnowStmt {
    pub facts: Vec<Fact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl KnowStmt {
    pub fn new(facts: Vec<Fact>, line_file_index: Option<(usize, usize)>) -> Self {
        KnowStmt { facts, line_file_index }
    }
}

impl fmt::Display for KnowStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "know {}", self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>().join(", "))
    }
}