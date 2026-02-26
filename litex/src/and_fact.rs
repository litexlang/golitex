use crate::specific_fact::SpecFact;
use std::fmt;
use crate::consts::AND;
use crate::helper::str_with_line_file;

pub struct AndFact {
    pub facts: Vec<Box<SpecFact>>,
    pub line: u32,
    pub file_index: usize,
}

impl AndFact {
    pub fn new(facts: Vec<Box<SpecFact>>, line: u32, file_index: usize) -> Self {
        AndFact { facts, line, file_index }
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

impl fmt::Display for AndFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // join by " and "
        write!(f, "{}", self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>().join(format!(" {} ", AND).as_str()))
    }
}