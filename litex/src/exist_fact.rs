use std::fmt;
use crate::keywords::{EXIST, LEFT_CURLY_BRACE, NOT,  RIGHT_CURLY_BRACE, ST};
use crate::helper::{curly_braced_vec_to_string_with_sep, vec_to_string_join_by_comma};
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::parameter_type_and_property::ParamDefWithParamTypeAndProperty;

#[derive(Clone)]
pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

#[derive(Clone)]
pub struct TrueExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl TrueExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
        facts: Vec<OrFactOrAndFactOrSpecFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        TrueExistFact { params_def_with_type, facts, line_file_index }
    }
}

impl NotExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
        facts: Vec<OrFactOrAndFactOrSpecFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        NotExistFact { params_def_with_type, facts, line_file_index }
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

pub fn line_file(e: &ExistFact) -> Option<(usize, usize)> {
    match e {
        ExistFact::TrueExistFact(x) => x.line_file_index,
        ExistFact::NotExistFact(x) => x.line_file_index,
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
    pub fn is_true(&self) -> bool {
        match self {
            ExistFact::TrueExistFact(_) => true,
            ExistFact::NotExistFact(_) => false,
        }
    }

    pub fn facts(&self) -> &Vec<OrFactOrAndFactOrSpecFact> {
        match self {
            ExistFact::TrueExistFact(x) => &x.facts,
            ExistFact::NotExistFact(x) => &x.facts,
        }
    }

    pub fn key(&self) -> String {
        return format!("{} {}{}{}", EXIST, LEFT_CURLY_BRACE, vec_to_string_join_by_comma(&self.facts().iter().map(|fact| fact.key()).collect::<Vec<String>>()), RIGHT_CURLY_BRACE);
    }
}

