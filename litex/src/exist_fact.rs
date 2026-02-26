use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::consts::{EXIST, NOT, ST};
use crate::helper::{braced_vec_to_string, vec_pair_to_string_ab};
use crate::parameter_set::ParameterSet;

pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

pub struct TrueExistFact {
    pub exist_params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub facts: Vec<Box<AtomicFact>>,
    pub line: u32,
}

pub struct NotExistFact {
    pub exist_params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub facts: Vec<Box<AtomicFact>>,
    pub line: u32,
}

impl TrueExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        facts: Vec<Box<AtomicFact>>,
        line: u32,
    ) -> Self {
        TrueExistFact { exist_params, param_sets, facts, line }
    }
}

impl NotExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        facts: Vec<Box<AtomicFact>>,
        line: u32,
    ) -> Self {
        NotExistFact { exist_params, param_sets, facts, line }
    }
}

impl fmt::Display for TrueExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{} {} {}", EXIST, vec_pair_to_string_ab(&self.exist_params, &self.param_sets), ST, braced_vec_to_string(&self.facts))
    }
}

impl fmt::Display for NotExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {} {}", NOT, EXIST, vec_pair_to_string_ab(&self.exist_params, &self.param_sets), ST, braced_vec_to_string(&self.facts))
    }
}

impl ExistFact {
    pub fn line(&self) -> u32 {
        match self {
            ExistFact::TrueExistFact(x) => x.line,
            ExistFact::NotExistFact(x) => x.line,
        }
    }
}

impl fmt::Display for ExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistFact::TrueExistFact(x) => write!(f, "{}", x),
            ExistFact::NotExistFact(x) => write!(f, "{}", x),
        }
    }
}