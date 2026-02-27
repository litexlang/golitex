use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::consts::{EXIST, NOT, ST};
use crate::helper::{curly_braced_vec_to_string_with_sep, str_with_line_file, vec_pair_to_string};
use crate::parameter_set::ParameterSet;

pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

pub struct TrueExistFact {
    pub exist_params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub facts: Vec<AtomicFact>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotExistFact {
    pub exist_params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub facts: Vec<AtomicFact>,
    pub line: u32,
    pub file_index: usize,
}

impl TrueExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        facts: Vec<AtomicFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        TrueExistFact { exist_params, param_sets, facts, line, file_index }
    }
}

impl NotExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        facts: Vec<AtomicFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        NotExistFact { exist_params, param_sets, facts, line, file_index }
    }
}

impl fmt::Display for TrueExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            1 => write!(f, "{} {} {} {}", EXIST, vec_pair_to_string(&self.exist_params, &self.param_sets), ST, self.facts[0]),
            _ => write!(f, "{} {} {} {}", EXIST, vec_pair_to_string(&self.exist_params, &self.param_sets), ST, curly_braced_vec_to_string_with_sep(&self.facts, ", ")),
        }
    }
}

impl fmt::Display for NotExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            1 => write!(f, "{} {} {} {} {}", NOT, EXIST, vec_pair_to_string(&self.exist_params, &self.param_sets), ST, self.facts[0]),
            _ => write!(f, "{} {} {} {} {}", NOT, EXIST, vec_pair_to_string(&self.exist_params, &self.param_sets), ST, curly_braced_vec_to_string_with_sep(&self.facts, ", ")),
        }
    }
}

impl ExistFact {
    pub fn line(&self) -> u32 {
        match self {
            ExistFact::TrueExistFact(x) => x.line,
            ExistFact::NotExistFact(x) => x.line,
        }
    }

    pub fn file_index(&self) -> usize {
        match self {
            ExistFact::TrueExistFact(x) => x.file_index,
            ExistFact::NotExistFact(x) => x.file_index,
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

impl ExistFact {
    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line(), self.file_index());
    }
}