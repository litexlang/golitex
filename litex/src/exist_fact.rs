use std::fmt;
use crate::consts::{EXIST, NOT, ST};
use crate::helper::{curly_braced_vec_to_string_with_sep, vec_to_string_join_by_comma};
use crate::parameter_type_and_property::ParamDefWithParamTypeAndProperty;
use crate::specific_fact::SpecFact;

pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

pub enum SpecFactOrAndFactWithSpecFacts {
    SpecFact(SpecFact),
    AndFactWithSpecFacts(Vec<SpecFact>),
}

pub struct TrueExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub facts: Vec<SpecFactOrAndFactWithSpecFacts>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub facts: Vec<SpecFactOrAndFactWithSpecFacts>,
    pub line: u32,
    pub file_index: usize,
}

impl TrueExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
        facts: Vec<SpecFactOrAndFactWithSpecFacts>,
        line: u32,
        file_index: usize,
    ) -> Self {
        TrueExistFact { params_def_with_type, facts, line, file_index }
    }
}

impl NotExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
        facts: Vec<SpecFactOrAndFactWithSpecFacts>,
        line: u32,
        file_index: usize,
    ) -> Self {
        NotExistFact { params_def_with_type, facts, line, file_index }
    }
}

impl TrueExistFact {
    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        match self.facts.len() {
            1 => format!("{} {} {}", vec_to_string_join_by_comma(&self.params_def_with_type), ST, self.facts[0].to_string()),
            _ => format!("{} {} {}", vec_to_string_join_by_comma(&self.params_def_with_type), ST, curly_braced_vec_to_string_with_sep(&self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>(), ", ")),
        }
    }
}

impl NotExistFact {
    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        match self.facts.len() {
            1 => format!("{} {} {}", vec_to_string_join_by_comma(&self.params_def_with_type), ST, self.facts[0].to_string()),
            _ => format!("{} {} {}", vec_to_string_join_by_comma(&self.params_def_with_type), ST, curly_braced_vec_to_string_with_sep(&self.facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>(), ", ")),
        }
    }
}

impl fmt::Display for TrueExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return write!(f, "{} {}", EXIST, self.exist_fact_string_without_exist_as_prefix());
    }
}

impl fmt::Display for NotExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return write!(f, "{} {} {}", NOT, EXIST, self.exist_fact_string_without_exist_as_prefix());
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


impl fmt::Display for SpecFactOrAndFactWithSpecFacts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpecFactOrAndFactWithSpecFacts::SpecFact(spec_fact) => write!(f, "{}", spec_fact),
            SpecFactOrAndFactWithSpecFacts::AndFactWithSpecFacts(and_fact_with_spec_facts) => write!(f, "{}", vec_to_string_join_by_comma(and_fact_with_spec_facts)),
        }
    }
}
