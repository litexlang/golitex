use std::fmt;
use crate::fact::Fact;

pub struct KnowStmt {
    pub facts: Vec<Fact>,
    pub line_file: (usize, usize),
}

impl KnowStmt {
    pub fn new(facts: Vec<Fact>, line_file: (usize, usize)) -> Self {
        KnowStmt { facts, line_file }
    }

    pub fn stmt_type_name(&self) -> String {
        "KnowStmt".to_string()
    }
}

impl fmt::Display for KnowStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "know {}", self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>().join(", "))
    }
}