use std::fmt;
use crate::common::keywords::{AND, FACT_PREFIX, OR, is_comparison_str};
use crate::common::helper::vec_to_string_with_sep;
use super::atomic_fact::AtomicFact;
use crate::obj::Obj;
use crate::obj::IdentifierOrIdentifierWithMod;

#[derive(Clone)]
pub struct AndAtomicFact {
    pub facts: Vec<AtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl AndAtomicFact {
    pub fn new(facts: Vec<AtomicFact>, line_file_index: Option<(usize, usize)>) -> Self {
        AndAtomicFact { facts, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

#[derive(Clone)]
pub struct ChainAtomicFact {
    pub objs: Vec<Obj>,
    pub prop_names: Vec<IdentifierOrIdentifierWithMod>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ChainAtomicFact {
    pub fn new(
        objs: Vec<Obj>,
        prop_names: Vec<IdentifierOrIdentifierWithMod>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        ChainAtomicFact { objs, prop_names, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

#[derive(Clone)]
pub enum MatchableFactWithAtomicFactInside {
    AtomicFact(AtomicFact),
    AndAtomicFact(AndAtomicFact),
    ChainAtomicFact(ChainAtomicFact),
}

#[derive(Clone)]
pub struct OrAtomicFact {
    pub facts: Vec<MatchableFactWithAtomicFactInside>,
    pub line_file_index: Option<(usize, usize)>,
}

impl OrAtomicFact {
    pub fn new(facts: Vec<MatchableFactWithAtomicFactInside>, line_file_index: Option<(usize, usize)>) -> Self {
        OrAtomicFact { facts, line_file_index }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }
}

impl fmt::Display for AndAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts, format!(" {} ", AND).as_str()))
    }
}

impl AndAtomicFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.facts.iter().map(|a| a.key()).collect::<Vec<_>>(), format!(" {} ", AND).as_str())
    }
}

impl fmt::Display for ChainAtomicFact {
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

impl ChainAtomicFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.prop_names.iter().map(|p| p.to_string()).collect::<Vec<_>>(), format!(" {} ", AND).as_str())
    }
}

impl fmt::Display for MatchableFactWithAtomicFactInside {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatchableFactWithAtomicFactInside::AtomicFact(a) => write!(f, "{}", a),
            MatchableFactWithAtomicFactInside::AndAtomicFact(a) => write!(f, "{}", a),
            MatchableFactWithAtomicFactInside::ChainAtomicFact(c) => write!(f, "{}", c),
        }
    }
}

impl MatchableFactWithAtomicFactInside {
    pub fn key(&self) -> String {
        match self {
            MatchableFactWithAtomicFactInside::AtomicFact(a) => a.key(),
            MatchableFactWithAtomicFactInside::AndAtomicFact(a) => a.key(),
            MatchableFactWithAtomicFactInside::ChainAtomicFact(c) => c.key(),
        }
    }
}

impl fmt::Display for OrAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", vec_to_string_with_sep(&self.facts.iter().map(|x| x.to_string()).collect::<Vec<_>>(), format!(" {} ", OR).as_str()))
    }
}

impl OrAtomicFact {
    pub fn key(&self) -> String {
        vec_to_string_with_sep(&self.facts.iter().map(|x| x.key()).collect::<Vec<_>>(), format!(" {} ", OR).as_str())
    }
}
