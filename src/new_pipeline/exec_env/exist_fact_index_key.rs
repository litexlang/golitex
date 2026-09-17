//! Index key for known_exist / forall exist conclusions.
//! Exist bodies are only atomic / and / chain / or, so this key is easy to design
//! and known-exist search stays a simple shape bucket + exact/unify match.
//! Exact match is separate: known uses alpha body equality; forall uses unify.

use crate::new_pipeline::ast::fact::{ExistFact, QuantifierFreeFact};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::param::TypedParameterList;
use crate::new_pipeline::exec_env::or_fact_index_key::{
    atomic_fact_shape, or_fact_index_key, AtomicAndChainFactShape, AtomicFactShape,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExistFactKind {
    Plain,
    Unique,
    Not,
}

// Shape of one exist body clause (mirrors QuantifierFreeFact, without objs).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum QuantifierFreeShape {
    Atomic(AtomicFactShape),
    And {
        components: Vec<AtomicFactShape>,
    },
    Chain {
        n_objs: usize,
        props: Vec<AtomicName>,
    },
    Or {
        branches: Vec<AtomicAndChainFactShape>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExistFactIndexKey {
    pub kind: ExistFactKind,
    pub n_params: usize,
    pub body_shape: Vec<QuantifierFreeShape>,
}

pub fn exist_fact_index_key(exist: &ExistFact) -> ExistFactIndexKey {
    let (kind, plain) = match exist {
        ExistFact::PlainExistFact(p) => (ExistFactKind::Plain, p),
        ExistFact::ExistUniqueFact(p) => (ExistFactKind::Unique, p),
        ExistFact::NotExistFact(p) => (ExistFactKind::Not, p),
    };
    ExistFactIndexKey {
        kind,
        n_params: typed_parameter_count(&plain.typed_parameters),
        body_shape: plain.facts.iter().map(quantifier_free_shape).collect(),
    }
}

// Lookup keys for a goal: plain may also hit Unique buckets (exist! ⇒ exist).
pub fn exist_fact_known_lookup_keys(goal: &ExistFact) -> Vec<ExistFactIndexKey> {
    let primary = exist_fact_index_key(goal);
    let mut keys = vec![primary.clone()];
    if matches!(goal, ExistFact::PlainExistFact(_)) {
        keys.push(ExistFactIndexKey {
            kind: ExistFactKind::Unique,
            n_params: primary.n_params,
            body_shape: primary.body_shape.clone(),
        });
    }
    keys
}

fn typed_parameter_count(params: &TypedParameterList) -> usize {
    params.groups.iter().map(|g| g.params.len()).sum()
}

fn quantifier_free_shape(fact: &QuantifierFreeFact) -> QuantifierFreeShape {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => QuantifierFreeShape::Atomic(atomic_fact_shape(a)),
        QuantifierFreeFact::AndFact(a) => QuantifierFreeShape::And {
            components: a.facts.iter().map(atomic_fact_shape).collect(),
        },
        QuantifierFreeFact::ChainFact(c) => QuantifierFreeShape::Chain {
            n_objs: c.objs.len(),
            props: c.prop_names.clone(),
        },
        QuantifierFreeFact::OrFact(o) => QuantifierFreeShape::Or {
            branches: or_fact_index_key(o).branches,
        },
    }
}
