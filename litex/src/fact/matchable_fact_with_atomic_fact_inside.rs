use std::fmt;
use crate::common::keywords::{AND, FACT_PREFIX,  is_comparison_str};
use crate::common::helper::vec_to_string_with_sep;
use super::atomic_fact::{AtomicFact};
use super::fact::Fact;
use crate::error::NewAtomicFactError;
use crate::obj::Obj;
use crate::obj::IdentifierOrIdentifierWithMod;

#[derive(Clone)]
pub struct AndFact {
    pub facts: Vec<AtomicFact>,
    pub line_file_index: (usize, usize),
}

impl AndFact {
    pub fn new(facts: Vec<AtomicFact>, line_file_index: (usize, usize)) -> Self {
        AndFact { facts, line_file_index }
    }
    pub fn line_file_index(&self) -> (usize, usize) {
        self.line_file_index
    }
}

#[derive(Clone)]
pub struct ChainFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<IdentifierOrIdentifierWithMod>,
    pub line_file_index: (usize, usize),
}

impl ChainFact {
    pub fn new(
        objs: Vec<Obj>,
        prop_names: Vec<IdentifierOrIdentifierWithMod>,
        line_file_index: (usize, usize),
    ) -> Self {
        ChainFact { objs, prop_names, line_file_index }
    }
    pub fn line_file_index(&self) -> (usize, usize) {
        self.line_file_index
    }

    pub fn facts(&self) -> Result<Vec<AtomicFact>, NewAtomicFactError> {
        let mut facts = Vec::new();
        for (i, obj) in self.objs.iter().enumerate() {
            let prop_name = self.prop_names[i].clone();
            let atomic_fact = AtomicFact::to_atomic_fact(prop_name, true, vec![obj.clone()], self.line_file_index);
            facts.push(atomic_fact?);
        }
        Ok(facts)
    }
}

#[derive(Clone)]
pub enum ChainAtomicFact {
    AtomicFact(AtomicFact),
    ChainFact(ChainFact),
}

impl fmt::Display for ChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ChainAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            ChainAtomicFact::ChainFact(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Clone)]
pub enum AndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
}

impl fmt::Display for AndFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts, format!(" {} ", AND)))
    }
}

impl AndFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.facts.iter().map(|a| a.key()).collect::<Vec<_>>(), format!(" {} ", AND))
    }
}

impl fmt::Display for ChainFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = self.objs[0].to_string();
        for (i, obj) in self.objs[1..].iter().enumerate() {
            if is_comparison_str(&self.prop_names[i].to_string()) {
                s.push_str(&format!(" {} {}", self.prop_names[i], obj));
            } else {
                s.push_str(&format!(" {}{} {}", FACT_PREFIX, self.prop_names[i], obj));
            }
        }
        write!(f, "{}", s)
    }
}

impl ChainFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.prop_names.iter().map(|p| p.to_string()).collect::<Vec<_>>(), format!(" {} ", AND))
    }
}

impl fmt::Display for AndChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AndChainAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            AndChainAtomicFact::AndFact(a) => write!(f, "{}", a),
            AndChainAtomicFact::ChainFact(c) => write!(f, "{}", c),
        }
    }
}

impl AndChainAtomicFact {
    pub fn key(&self) -> String {
        match self {
            AndChainAtomicFact::AtomicFact(a) => a.key(),
            AndChainAtomicFact::AndFact(a) => a.key(),
            AndChainAtomicFact::ChainFact(c) => c.key(),
        }
    }

    pub fn to_fact(&self) -> Fact {
        match self {
            AndChainAtomicFact::AtomicFact(atomic_fact) => Fact::AtomicFact(atomic_fact.clone()),
            AndChainAtomicFact::AndFact(and_fact) => Fact::AndFact(and_fact.clone()),
            AndChainAtomicFact::ChainFact(chain_fact) => Fact::ChainFact(chain_fact.clone()),
        }
    }

    pub fn to_exist_or_and_chain_atomic_fact(&self) -> crate::fact::ExistOrAndChainAtomicFact {
        match self {
            AndChainAtomicFact::AtomicFact(atomic_fact) => crate::fact::ExistOrAndChainAtomicFact::AtomicFact(atomic_fact.clone()),
            AndChainAtomicFact::AndFact(and_fact) => crate::fact::ExistOrAndChainAtomicFact::AndFact(and_fact.clone()),
            AndChainAtomicFact::ChainFact(chain_fact) => crate::fact::ExistOrAndChainAtomicFact::ChainFact(chain_fact.clone()),
        }
    }
}

