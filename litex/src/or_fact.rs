use crate::consts::OR;
use std::fmt;
use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::helper::vec_to_string_with_sep;

#[derive(Clone)]
pub struct OrFact {
    pub facts: Vec<AndFactOrSpecFact>,
    pub line_file_index: Option<(u16, usize)>,
}

impl OrFact {
    pub fn new(facts: Vec<AndFactOrSpecFact>, line_file_index: Option<(u16, usize)>) -> Self {
        OrFact { facts, line_file_index }
    }
}

impl fmt::Display for OrFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 把这些fact用 " or " 连接起来
        let fact_strings = self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>();
        write!(f, "{}", fact_strings.join(format!(" {} ", OR).as_str()))
    }
}

impl OrFact {
    pub fn key(&self) -> String {
        return format!("{}", vec_to_string_with_sep(&self.facts.iter().map(|fact| fact.key()).collect::<Vec<String>>(), format!(" {} ", OR).as_str()));
    }
}