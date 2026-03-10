use std::fmt;
use crate::common::keywords::{AND, FACT_PREFIX,  is_comparison_str};
use crate::common::helper::vec_to_string_with_sep;
use super::atomic_fact::{AtomicFact};
use crate::error::NewAtomicFactError;
use crate::obj::Obj;
use crate::obj::IdentifierOrIdentifierWithMod;

#[derive(Clone)]
pub struct AndFact {
    pub facts: Vec<AtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl AndFact {
    pub fn new(facts: Vec<AtomicFact>, line_file_index: Option<(usize, usize)>) -> Self {
        AndFact { facts, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

#[derive(Clone)]
pub struct ChainFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<IdentifierOrIdentifierWithMod>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ChainFact {
    pub fn new(
        objs: Vec<Obj>,
        prop_names: Vec<IdentifierOrIdentifierWithMod>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        ChainFact { objs, prop_names, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
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
pub enum AndFactOrChainFactOrAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
}

impl fmt::Display for AndFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts, format!(" {} ", AND).as_str()))
    }
}

impl AndFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.facts.iter().map(|a| a.key()).collect::<Vec<_>>(), format!(" {} ", AND).as_str())
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
        vec_to_string_with_sep(&self.prop_names.iter().map(|p| p.to_string()).collect::<Vec<_>>(), format!(" {} ", AND).as_str())
    }
}

impl fmt::Display for AndFactOrChainFactOrAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AndFactOrChainFactOrAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            AndFactOrChainFactOrAtomicFact::AndFact(a) => write!(f, "{}", a),
            AndFactOrChainFactOrAtomicFact::ChainFact(c) => write!(f, "{}", c),
        }
    }
}

impl AndFactOrChainFactOrAtomicFact {
    pub fn key(&self) -> String {
        match self {
            AndFactOrChainFactOrAtomicFact::AtomicFact(a) => a.key(),
            AndFactOrChainFactOrAtomicFact::AndFact(a) => a.key(),
            AndFactOrChainFactOrAtomicFact::ChainFact(c) => c.key(),
        }
    }
}

