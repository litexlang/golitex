//! Surface facts with no inline quantifier: atomic, conjunction, relation chain, or disjunction.
//!
//! A named atomic proposition may still refer to a definition containing quantifiers. This type
//! constrains the direct AST shape used by existential specs, set builders, and similar bodies.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum QuantifierFreeFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
}

impl QuantifierFreeFact {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        match self {
            QuantifierFreeFact::AtomicFact(a) => {
                QuantifierFreeFact::AtomicFact(a.replace_bound_identifier(from, to))
            }
            QuantifierFreeFact::AndFact(af) => QuantifierFreeFact::AndFact(AndFact::new(
                af.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                af.line_file,
            )),
            QuantifierFreeFact::ChainFact(cf) => QuantifierFreeFact::ChainFact(ChainFact::new(
                cf.objs
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
                cf.prop_names,
                cf.line_file,
            )),
            QuantifierFreeFact::OrFact(of) => QuantifierFreeFact::OrFact(OrFact::new(
                of.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                of.line_file,
            )),
        }
    }
}

impl From<AtomicFact> for QuantifierFreeFact {
    fn from(atomic_fact: AtomicFact) -> Self {
        QuantifierFreeFact::AtomicFact(atomic_fact)
    }
}

impl From<GreaterEqualFact> for QuantifierFreeFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<LessFact> for QuantifierFreeFact {
    fn from(f: LessFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<EqualFact> for QuantifierFreeFact {
    fn from(f: EqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl fmt::Display for QuantifierFreeFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            QuantifierFreeFact::AtomicFact(a) => write!(f, "{}", a),
            QuantifierFreeFact::AndFact(a) => write!(f, "{}", a),
            QuantifierFreeFact::ChainFact(c) => write!(f, "{}", c),
            QuantifierFreeFact::OrFact(o) => write!(f, "{}", o),
        }
    }
}

impl QuantifierFreeFact {
    pub fn key(&self) -> String {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.key(),
            QuantifierFreeFact::AndFact(a) => a.key(),
            QuantifierFreeFact::ChainFact(c) => c.key(),
            QuantifierFreeFact::OrFact(o) => o.key(),
        }
    }

    pub fn line_file(&self) -> LineFile {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.line_file(),
            QuantifierFreeFact::AndFact(a) => a.line_file(),
            QuantifierFreeFact::ChainFact(c) => c.line_file(),
            QuantifierFreeFact::OrFact(o) => o.line_file.clone(),
        }
    }
}

impl QuantifierFreeFact {
    pub fn from_ref_to_cloned_fact(&self) -> Fact {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.clone().into(),
            QuantifierFreeFact::AndFact(a) => a.clone().into(),
            QuantifierFreeFact::ChainFact(c) => c.clone().into(),
            QuantifierFreeFact::OrFact(o) => o.clone().into(),
        }
    }

    pub fn to_fact(self) -> Fact {
        match self {
            QuantifierFreeFact::AtomicFact(a) => Fact::AtomicFact(a),
            QuantifierFreeFact::AndFact(a) => Fact::AndFact(a),
            QuantifierFreeFact::ChainFact(c) => Fact::ChainFact(c),
            QuantifierFreeFact::OrFact(o) => Fact::OrFact(o),
        }
    }

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.get_args_from_fact(),
            QuantifierFreeFact::AndFact(a) => a.get_args_from_fact(),
            QuantifierFreeFact::ChainFact(c) => c.get_args_from_fact(),
            QuantifierFreeFact::OrFact(o) => o.get_args_from_fact(),
        }
    }

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        match self {
            QuantifierFreeFact::AtomicFact(a) => a.get_args_from_fact_ref(),
            QuantifierFreeFact::AndFact(a) => a.get_args_from_fact_ref(),
            QuantifierFreeFact::ChainFact(c) => c.get_args_from_fact_ref(),
            QuantifierFreeFact::OrFact(o) => o.get_args_from_fact_ref(),
        }
    }
}
