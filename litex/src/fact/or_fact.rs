use crate::common::keywords::OR;
use std::fmt;
use crate::common::helper::vec_to_string_with_sep;
use crate::fact::matchable_fact_with_atomic_fact_inside::AndChainAtomicFact;

#[derive(Clone)]
pub struct OrFact {
    pub facts: Vec<AndChainAtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl OrFact {
    pub fn new(facts: Vec<AndChainAtomicFact>, line_file_index: Option<(usize, usize)>) -> Self {
        OrFact { facts, line_file_index }
    }
}

impl fmt::Display for OrFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fact_strings = self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>();
        write!(f, "{}", fact_strings.join(format!(" {} ", OR).as_str()))
    }
}

impl OrFact {
    pub fn key(&self) -> String {
        return format!("{}", vec_to_string_with_sep(&self.facts.iter().map(|fact| fact.key()).collect::<Vec<String>>(), format!(" {} ", OR)));
    }
}