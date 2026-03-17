use std::fmt;
use crate::common::keywords::{COMMA, EXIST, LEFT_CURLY_BRACE, RIGHT_CURLY_BRACE, ST};
use crate::common::helper::{curly_braced_vec_to_string_with_sep, vec_to_string_join_by_comma};
use crate::stmt::parameter_def::ParamDefWithParamType;
use super::atomic_fact::AtomicFact;
use super::matchable_fact_with_atomic_fact_inside::{AndFact, ChainFact};
use super::or_fact::OrFact;
use super::fact_inside_forall::ExistOrAndChainAtomicFact;
use super::fact::Fact;

#[derive(Clone)]
pub enum OrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
}

impl OrAndChainAtomicFact {
    pub fn to_exist_or_and_chain_atomic_fact(self) -> ExistOrAndChainAtomicFact {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            OrAndChainAtomicFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
            OrAndChainAtomicFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
            OrAndChainAtomicFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
        }
    }
}

#[derive(Clone)]
pub struct ExistFact {
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ExistFact {
    pub fn new(
        params_def_with_type: Vec<ParamDefWithParamType>,
        facts: Vec<OrAndChainAtomicFact>,
        line_file_index: Option<(usize, usize)>,
    ) -> Self {
        ExistFact { params_def_with_type, facts, line_file_index }
    }

    pub fn exist_fact_string_without_exist_as_prefix(&self) -> String {
        exist_fact_string_without_exist_as_prefix(&self.params_def_with_type, &self.facts)
    }

    pub fn key(&self) -> String {
        format!("{} {}{}{}", EXIST, LEFT_CURLY_BRACE, vec_to_string_join_by_comma(&self.facts.iter().map(|fact| fact.key()).collect::<Vec<String>>()), RIGHT_CURLY_BRACE)
    }

    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        self.line_file_index
    }

    pub fn params_def_with_type(&self) -> &Vec<ParamDefWithParamType> {
        &self.params_def_with_type
    }

    pub fn facts(&self) -> &Vec<OrAndChainAtomicFact> {
        &self.facts
    }
}

fn exist_fact_string_without_exist_as_prefix(param_defs: &Vec<ParamDefWithParamType>, facts: &Vec<OrAndChainAtomicFact>) -> String {
    format!("{} {} {}", vec_to_string_join_by_comma(param_defs), ST, curly_braced_vec_to_string_with_sep(&facts.iter().map(|fact| fact.to_string()).collect::<Vec<String>>(), format!("{} ", COMMA)))
}

impl fmt::Display for ExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", EXIST, self.exist_fact_string_without_exist_as_prefix())
    }
}

// ---------- Display & key for FactInsideExistFact ----------
impl fmt::Display for OrAndChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => write!(f, "{}", a),
            OrAndChainAtomicFact::AndFact(a) => write!(f, "{}", a),
            OrAndChainAtomicFact::ChainFact(c) => write!(f, "{}", c),
            OrAndChainAtomicFact::OrFact(o) => write!(f, "{}", o),
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn key(&self) -> String {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.key(),
            OrAndChainAtomicFact::AndFact(a) => a.key(),
            OrAndChainAtomicFact::ChainFact(c) => c.key(),
            OrAndChainAtomicFact::OrFact(o) => o.key(),
        }
    }
    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        match self {
            OrAndChainAtomicFact::AtomicFact(_) => None,
            OrAndChainAtomicFact::AndFact(a) => a.line_file_index(),
            OrAndChainAtomicFact::ChainFact(c) => c.line_file_index(),
            OrAndChainAtomicFact::OrFact(o) => o.line_file_index,
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn from_ref_to_cloned_fact(&self) -> Fact {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => Fact::AtomicFact(a.clone()),
            OrAndChainAtomicFact::AndFact(a) => Fact::AndFact(a.clone()),
            OrAndChainAtomicFact::ChainFact(c) => Fact::ChainFact(c.clone()),
            OrAndChainAtomicFact::OrFact(o) => Fact::OrFact(o.clone()),
        }
    }

    pub fn to_fact(self) -> Fact {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => Fact::AtomicFact(a),
            OrAndChainAtomicFact::AndFact(a) => Fact::AndFact(a),
            OrAndChainAtomicFact::ChainFact(c) => Fact::ChainFact(c),
            OrAndChainAtomicFact::OrFact(o) => Fact::OrFact(o),
        }
    }
}
