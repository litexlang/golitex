use crate::specific_fact::SpecFact;
use std::fmt;
use crate::consts::{AND, FACT_PREFIX};
use crate::obj::Obj;
use crate::atom::Atom;
use crate::helper::vec_to_string_with_sep;

pub enum AndFact {
    AndSpecFacts(AndSpecFacts),
    ChainFact(ChainFact),
}

pub struct AndSpecFacts {
    pub facts: Vec<SpecFact>,
    pub line: u32,
    pub file_index: usize,
}

pub struct ChainFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<Atom>,
    pub line: u32,
    pub file_index: usize,
}


impl AndSpecFacts {
    pub fn new(facts: Vec<SpecFact>, line: u32, file_index: usize) -> Self {
        AndSpecFacts { facts, line, file_index }
    }
}

impl fmt::Display for AndSpecFacts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts, format!(" {} ", AND).as_str()))
    }
}

impl ChainFact {
    pub fn new(objs: Vec<Obj>, prop_names: Vec<Atom>, line: u32, file_index: usize) -> Self {
        ChainFact { objs, prop_names, line, file_index }
    }
}

impl fmt::Display for ChainFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        result.push_str(&self.objs[0].to_string());
        
        for i in 1..self.objs.len() {
            result.push_str(&format!(" {}{}", FACT_PREFIX, self.prop_names[i - 1]));
            result.push_str(&format!(" {} {}", AND, self.objs[i].to_string()));
        }
        write!(f, "{}", result)
    }
}

impl fmt::Display for AndFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AndFact::AndSpecFacts(and_spec_facts) => write!(f, "{}", and_spec_facts),
            AndFact::ChainFact(chain_facts) => write!(f, "{}", chain_facts),
        }
    }
}

impl AndFact {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            AndFact::AndSpecFacts(and_spec_facts) => (and_spec_facts.line, and_spec_facts.file_index),
            AndFact::ChainFact(chain_facts) => (chain_facts.line, chain_facts.file_index),
        }
    }

    pub fn key(&self) -> String {
        match self {
            AndFact::AndSpecFacts(and_spec_facts) => and_spec_facts.key(),
            AndFact::ChainFact(chain_facts) => chain_facts.key(),
        }
    }
}

impl AndSpecFacts {
    pub fn key(&self) -> String {
        return format!("{}", vec_to_string_with_sep(&self.facts.iter().map(|fact| fact.key()).collect::<Vec<String>>(), format!(" {} ", AND).as_str()));
    }
}

impl ChainFact {
    pub fn key(&self) -> String {
        return format!("{}", vec_to_string_with_sep(&self.prop_names.iter().map(|prop_name| prop_name.to_string()).collect::<Vec<String>>(), format!(" {} ", AND).as_str()));
    }
}
