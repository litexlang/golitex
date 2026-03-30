use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct OrFact {
    pub facts: Vec<AndChainAtomicFact>,
    pub line_file: (usize, usize),
}

impl OrFact {
    pub fn new(facts: Vec<AndChainAtomicFact>, line_file: (usize, usize)) -> Self {
        OrFact { facts, line_file }
    }
}

impl fmt::Display for OrFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fact_strings = self
            .facts
            .iter()
            .map(|fact| fact.to_string())
            .collect::<Vec<String>>();
        write!(f, "{}", fact_strings.join(format!(" {} ", OR).as_str()))
    }
}

impl OrFact {
    pub fn key(&self) -> String {
        return format!(
            "{}",
            vec_to_string_with_sep(
                &self
                    .facts
                    .iter()
                    .map(|fact| fact.key())
                    .collect::<Vec<String>>(),
                format!(" {} ", OR)
            )
        );
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        let mut result: Vec<Obj> = Vec::new();
        for and_chain_atomic_fact in self.facts.iter() {
            let args_from_branch = and_chain_atomic_fact.get_args_from_fact();
            for arg in args_from_branch {
                result.push(arg);
            }
        }
        result
    }
}
