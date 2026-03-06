use crate::specific_fact::SpecFact;
use crate::atomic_fact::AtomicFact;
use crate::errors::NewAtomicFactError;
use std::fmt;
use crate::keywords::{AND, FACT_PREFIX};
use crate::obj::Obj;
use crate::atom::IdentifierOrIdentifierWithMod;
use crate::helper::vec_to_string_with_sep;

#[derive(Clone)]
pub enum AndFact {
    AndSpecFacts(AndSpecFacts),
    ChainFact(ChainFact),
}

#[derive(Clone)]
pub struct AndSpecFacts {
    pub facts: Vec<SpecFact>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct ChainFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<IdentifierOrIdentifierWithMod>,
    pub line_file_index: Option<(usize, usize)>,
}


impl AndSpecFacts {
    pub fn new(facts: Vec<SpecFact>, line_file_index: Option<(usize, usize)>) -> Self {
        AndSpecFacts { facts, line_file_index }
    }
}

impl fmt::Display for AndSpecFacts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts, format!(" {} ", AND).as_str()))
    }
}

impl ChainFact {
    pub fn new(objs: Vec<Obj>, prop_names: Vec<IdentifierOrIdentifierWithMod>, line_file_index: Option<(usize, usize)>) -> Self {
        ChainFact { objs, prop_names, line_file_index }
    }
}

impl fmt::Display for ChainFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        result.push_str(&self.objs[0].to_string());
        
        for (i, x) in self.objs[1..].iter().enumerate() {
            result.push_str(&format!(" {}{}", FACT_PREFIX, self.prop_names[i]));
            result.push_str(&format!(" {} {}", AND, x.to_string()));
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
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            AndFact::AndSpecFacts(and_spec_facts) => and_spec_facts.line_file_index,
            AndFact::ChainFact(chain_facts) => chain_facts.line_file_index,
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

impl ChainFact {
    pub fn facts(&self) -> Result<Vec<SpecFact>, NewAtomicFactError> {
        let mut facts = Vec::new();
        for prop_name in self.prop_names.iter() {
            let fact = AtomicFact::to_atomic_fact(prop_name.clone(), true, Vec::new(), self.line_file_index);
            if fact.is_err() {
                return Err(fact.err().unwrap());
            }
            facts.push(SpecFact::AtomicFact(fact.unwrap()));
        }
        Ok(facts)
    }
}