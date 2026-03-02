use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::consts::{EXIST, NOT, ST};
use crate::helper::{curly_braced_vec_to_string_with_sep, vec_to_string_join_by_comma};
use crate::parameter_type_and_property::ParamDefWithParamTypeAndProperty;

pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

impl ExistFact {
    pub fn params_def_with_type(&self) -> &Vec<ParamDefWithParamTypeAndProperty> {
        match self {
            ExistFact::TrueExistFact(x) => &x.params_def_with_type,
            ExistFact::NotExistFact(x) => &x.params_def_with_type,
        }
    }

    pub fn facts(&self) -> &Vec<AtomicFact> {
        match self {
            ExistFact::TrueExistFact(x) => &x.facts,
            ExistFact::NotExistFact(x) => &x.facts,
        }
    }
}

pub struct TrueExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub facts: Vec<AtomicFact>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub facts: Vec<AtomicFact>,
    pub line: u32,
    pub file_index: usize,
}

impl TrueExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
        facts: Vec<AtomicFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        TrueExistFact { params_def_with_type, facts, line, file_index }
    }
}

impl NotExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
        facts: Vec<AtomicFact>,
        line: u32,
        file_index: usize,
    ) -> Self {
        NotExistFact { params_def_with_type, facts, line, file_index }
    }
}

impl fmt::Display for TrueExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            1 => write!(f, "{} {} {} {}", EXIST, vec_to_string_join_by_comma(&self.params_def_with_type), ST, self.facts[0]),
            _ => write!(f, "{} {} {} {}", EXIST, vec_to_string_join_by_comma(&self.params_def_with_type), ST, curly_braced_vec_to_string_with_sep(&self.facts, ", ")),
        }
    }
}

impl fmt::Display for NotExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            1 => write!(f, "{} {} {} {} {}", NOT, EXIST, vec_to_string_join_by_comma(&self.params_def_with_type), ST, self.facts[0]),
            _ => write!(f, "{} {} {} {} {}", NOT, EXIST, vec_to_string_join_by_comma(&self.params_def_with_type), ST, curly_braced_vec_to_string_with_sep(&self.facts, ", ")),
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