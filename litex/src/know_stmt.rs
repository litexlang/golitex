use std::fmt;
use crate::fact::Fact;

pub struct KnowStmt {
    pub facts: Vec<Fact>,
    pub line: u32,
    pub file_index: usize,
}

impl KnowStmt {
    pub fn new(facts: Vec<Fact>, line: u32, file_index: usize) -> Self {
        KnowStmt { facts, line, file_index }
    }

    pub fn line_file(&self) -> (u32, usize) {
        (self.line, self.file_index)
    }
}

impl fmt::Display for KnowStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "know {}", self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>().join(", "))
    }
}