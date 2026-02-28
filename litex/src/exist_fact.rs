use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::consts::{EXIST, NOT, ST};
use crate::helper::{curly_braced_vec_to_string_with_sep, vec_pair_to_string};
use crate::parameter_type::ParameterType;

pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

pub struct TrueExistFact {
    pub exist_params: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub facts: Vec<AtomicFact>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotExistFact {
    pub exist_params: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub facts: Vec<AtomicFact>,
    pub line: u32,
    pub file_index: usize,
}

impl TrueExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterType>,
        facts: Vec<AtomicFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        TrueExistFact { exist_params, param_types: param_sets, facts, line, file_index }
    }
}

impl NotExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterType>,
        facts: Vec<AtomicFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        NotExistFact { exist_params, param_types: param_sets, facts, line, file_index }
    }
}

impl fmt::Display for TrueExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            1 => write!(f, "{} {} {} {}", EXIST, vec_pair_to_string(&self.exist_params, &self.param_types), ST, self.facts[0]),
            _ => write!(f, "{} {} {} {}", EXIST, vec_pair_to_string(&self.exist_params, &self.param_types), ST, curly_braced_vec_to_string_with_sep(&self.facts, ", ")),
        }
    }
}

impl fmt::Display for NotExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            1 => write!(f, "{} {} {} {} {}", NOT, EXIST, vec_pair_to_string(&self.exist_params, &self.param_types), ST, self.facts[0]),
            _ => write!(f, "{} {} {} {} {}", NOT, EXIST, vec_pair_to_string(&self.exist_params, &self.param_types), ST, curly_braced_vec_to_string_with_sep(&self.facts, ", ")),
        }
    }
}

/// 从 ExistFact 取得 line 与 file_index
pub fn line_file(e: &ExistFact) -> (u32, usize) {
    match e {
        ExistFact::TrueExistFact(x) => (x.line, x.file_index),
        ExistFact::NotExistFact(x) => (x.line, x.file_index),
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