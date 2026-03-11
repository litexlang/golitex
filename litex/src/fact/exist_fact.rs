use std::fmt;
use crate::common::keywords::{COMMA, EXIST, LEFT_CURLY_BRACE, NOT, RIGHT_CURLY_BRACE, ST};
use crate::common::helper::{curly_braced_vec_to_string_with_sep, vec_to_string_join_by_comma};
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;
use super::atomic_fact::AtomicFact;
use super::matchable_fact_with_atomic_fact_inside::{AndFact, ChainFact};
use super::or_fact::OrFact;
use super::fact_inside_forall::ExistOrAndChainAtomicFact;

/// Result of parsing after NOT: either an existential fact (not exist ...) or a single atomic fact (not $p(...)).
#[derive(Clone)]
pub enum ExistAtomicFact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
}

impl ExistAtomicFact {
    pub fn to_exist_or_and_chain_atomic_fact(self) -> ExistOrAndChainAtomicFact {
        match self {
            ExistAtomicFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            ExistAtomicFact::ExistFact(e) => ExistOrAndChainAtomicFact::ExistFact(e),
        }
    }
}

impl fmt::Display for ExistAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            ExistAtomicFact::ExistFact(e) => write!(f, "{}", e),
        }
    }
}

#[derive(Clone)]
pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

#[derive(Clone)]
pub enum OrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrAtomicFact(OrFact),
}

impl OrAndChainAtomicFact {
    pub fn to_exist_or_and_chain_atomic_fact(self) -> ExistOrAndChainAtomicFact {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            OrAndChainAtomicFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
            OrAndChainAtomicFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
            OrAndChainAtomicFact::OrAtomicFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
        }
    }
}

#[derive(Clone)]
pub struct TrueExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl TrueExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamType>,
        facts: Vec<OrAndChainAtomicFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        TrueExistFact { params_def_with_type, facts, line_file_index }
    }
}

impl NotExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamType>,
        facts: Vec<OrAndChainAtomicFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        NotExistFact { params_def_with_type, facts, line_file_index }
    }
}

fn exist_fact_string_without_exist_as_prefix(param_defs: &Vec<ParamDefWithParamType>, facts: &Vec<OrAndChainAtomicFact>) -> String {
    format!("{} {} {}", vec_to_string_join_by_comma(param_defs), ST, curly_braced_vec_to_string_with_sep(&facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>(), format!("{} ", COMMA).as_str()))
}

impl TrueExistFact {
    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        exist_fact_string_without_exist_as_prefix(&self.params_def_with_type, &self.facts)
    }
}

impl NotExistFact {
    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        exist_fact_string_without_exist_as_prefix(&self.params_def_with_type, &self.facts)
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

// ---------- Display & key for FactInsideExistFact ----------
impl fmt::Display for OrAndChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            OrAndChainAtomicFact::AndFact(a) => write!(f, "{}", a),
            OrAndChainAtomicFact::ChainFact(c) => write!(f, "{}", c),
            OrAndChainAtomicFact::OrAtomicFact(o) => write!(f, "{}", o),
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn key(&self) -> String {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.key(),
            OrAndChainAtomicFact::AndFact(a) => a.key(),
            OrAndChainAtomicFact::ChainFact(c) => c.key(),
            OrAndChainAtomicFact::OrAtomicFact(o) => o.key(),
        }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        match self {
            OrAndChainAtomicFact::AtomicFact(_) => None,
            OrAndChainAtomicFact::AndFact(a) => a.line_file_index(),
            OrAndChainAtomicFact::ChainFact(c) => c.line_file_index(),
            OrAndChainAtomicFact::OrAtomicFact(o) => o.line_file_index,
        }
    }
}

// ---------- line_file ----------
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

    pub fn facts(&self) -> &Vec<OrAndChainAtomicFact> {
        match self {
            ExistFact::TrueExistFact(x) => &x.facts,
            ExistFact::NotExistFact(x) => &x.facts,
        }
    }

    pub fn key(&self) -> String {
        format!("{} {}{}{}", EXIST, LEFT_CURLY_BRACE, vec_to_string_join_by_comma(&self.facts().iter().map(|fact| fact.key()).collect::<Vec<String>>()), RIGHT_CURLY_BRACE)
    }
}

