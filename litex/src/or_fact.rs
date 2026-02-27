use crate::consts::OR;
use std::fmt;
use crate::helper::str_with_line_file;
use crate::and_fact_or_specific_fact::AndFactOrSpecFact;

pub struct OrFact {
    pub facts: Vec<AndFactOrSpecFact>,
    pub line: u32,
    pub file_index: usize,
}

impl OrFact {
    pub fn new(facts: Vec<AndFactOrSpecFact>, line: u32, file_index: usize) -> Self {
        OrFact { facts, line, file_index }
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

impl fmt::Display for OrFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 把这些fact用 " or " 连接起来
        let fact_strings = self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>();
        write!(f, "{}", fact_strings.join(format!(" {} ", OR).as_str()))
    }
}