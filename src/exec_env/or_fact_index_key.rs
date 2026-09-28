//! Index key for known_or / forall or conclusions.
//! Exact arg match is separate; this key only carries branch shape.

use crate::ast::fact::{atomic_fact_args_ref, atomic_fact_has_positive_polarity};
use crate::ast::fact::{AndChainAtomicFact, AtomicFact, OrFact};
use crate::ast::names::AtomicName;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AtomicFactShape {
    pub prop: AtomicName,
    pub positive: bool,
    pub arity: usize,
}

// Shape of one or-branch (mirrors AndChainAtomicFact, without objs).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtomicAndChainFactShape {
    Atomic(AtomicFactShape),
    And {
        components: Vec<AtomicFactShape>,
    },
    Chain {
        n_objs: usize,
        props: Vec<AtomicName>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OrFactIndexKey {
    pub branches: Vec<AtomicAndChainFactShape>,
}

pub fn or_fact_index_key(or_fact: &OrFact) -> OrFactIndexKey {
    OrFactIndexKey {
        branches: or_fact.facts.iter().map(and_chain_fact_shape).collect(),
    }
}

pub(crate) fn and_chain_fact_shape(branch: &AndChainAtomicFact) -> AtomicAndChainFactShape {
    match branch {
        AndChainAtomicFact::AtomicFact(a) => AtomicAndChainFactShape::Atomic(atomic_fact_shape(a)),
        AndChainAtomicFact::AndFact(a) => AtomicAndChainFactShape::And {
            components: a.facts.iter().map(atomic_fact_shape).collect(),
        },
        AndChainAtomicFact::ChainFact(c) => AtomicAndChainFactShape::Chain {
            n_objs: c.objs.len(),
            props: c.prop_names.clone(),
        },
    }
}

pub(crate) fn atomic_fact_shape(fact: &AtomicFact) -> AtomicFactShape {
    AtomicFactShape {
        prop: fact.prop_name(),
        positive: atomic_fact_has_positive_polarity(fact),
        arity: atomic_fact_args_ref(fact).len(),
    }
}
