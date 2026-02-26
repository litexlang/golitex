use crate::specific_fact::SpecFact;
use crate::consts::OR;
use std::fmt;

pub struct OrFact {
    pub facts: Vec<Box<SpecFact>>,
    pub line: u32,
}

impl OrFact {
    pub fn new(facts: Vec<Box<SpecFact>>, line: u32) -> Self {
        OrFact { facts, line }
    }

    pub fn line(&self) -> u32 {
        self.line
    }
}

impl fmt::Display for OrFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 把这些fact用 " or " 连接起来
        let fact_strings = self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>();
        write!(f, "{}", fact_strings.join(format!(" {} ", OR).as_str()))
    }
}