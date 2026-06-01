//! Atomic / and / chain / or facts allowed in an `exist` body (`st { ... }`), without nesting `exist`.

use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum OrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
}

impl OrAndChainAtomicFact {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => {
                OrAndChainAtomicFact::AtomicFact(a.replace_bound_identifier(from, to))
            }
            OrAndChainAtomicFact::AndFact(af) => OrAndChainAtomicFact::AndFact(AndFact::new(
                af.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                af.line_file,
            )),
            OrAndChainAtomicFact::ChainFact(cf) => OrAndChainAtomicFact::ChainFact(ChainFact::new(
                cf.objs
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
                cf.prop_names,
                cf.line_file,
            )),
            OrAndChainAtomicFact::OrFact(of) => OrAndChainAtomicFact::OrFact(OrFact::new(
                of.facts
                    .into_iter()
                    .map(|x| x.replace_bound_identifier(from, to))
                    .collect(),
                of.line_file,
            )),
        }
    }
}

impl From<AtomicFact> for OrAndChainAtomicFact {
    fn from(atomic_fact: AtomicFact) -> Self {
        OrAndChainAtomicFact::AtomicFact(atomic_fact)
    }
}

impl From<GreaterEqualFact> for OrAndChainAtomicFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<LessFact> for OrAndChainAtomicFact {
    fn from(f: LessFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<EqualFact> for OrAndChainAtomicFact {
    fn from(f: EqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

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

    pub fn line_file(&self) -> LineFile {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.line_file(),
            OrAndChainAtomicFact::AndFact(a) => a.line_file(),
            OrAndChainAtomicFact::ChainFact(c) => c.line_file(),
            OrAndChainAtomicFact::OrFact(o) => o.line_file.clone(),
        }
    }
}

impl OrAndChainAtomicFact {
    pub fn from_ref_to_cloned_fact(&self) -> Fact {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.clone().into(),
            OrAndChainAtomicFact::AndFact(a) => a.clone().into(),
            OrAndChainAtomicFact::ChainFact(c) => c.clone().into(),
            OrAndChainAtomicFact::OrFact(o) => o.clone().into(),
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

    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.get_args_from_fact(),
            OrAndChainAtomicFact::AndFact(a) => a.get_args_from_fact(),
            OrAndChainAtomicFact::ChainFact(c) => c.get_args_from_fact(),
            OrAndChainAtomicFact::OrFact(o) => o.get_args_from_fact(),
        }
    }

    pub fn get_args_from_fact_ref(&self) -> Vec<&Obj> {
        match self {
            OrAndChainAtomicFact::AtomicFact(a) => a.get_args_from_fact_ref(),
            OrAndChainAtomicFact::AndFact(a) => a.get_args_from_fact_ref(),
            OrAndChainAtomicFact::ChainFact(c) => c.get_args_from_fact_ref(),
            OrAndChainAtomicFact::OrFact(o) => o.get_args_from_fact_ref(),
        }
    }
}
