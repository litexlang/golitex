use crate::ast::fact::{AndFact, ChainFact};
use crate::exec_env::or_fact_index_key::{atomic_fact_shape, AtomicFactShape};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AndForallConclusionIndexKey {
    pub components: Vec<AtomicFactShape>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ChainForallConclusionIndexKey {
    pub n_objs: usize,
    pub props: Vec<crate::ast::names::AtomicName>,
}

pub fn and_forall_conclusion_index_key(and_fact: &AndFact) -> AndForallConclusionIndexKey {
    AndForallConclusionIndexKey {
        components: and_fact.facts.iter().map(atomic_fact_shape).collect(),
    }
}

pub fn chain_forall_conclusion_index_key(chain_fact: &ChainFact) -> ChainForallConclusionIndexKey {
    ChainForallConclusionIndexKey {
        n_objs: chain_fact.objs.len(),
        props: chain_fact.prop_names.clone(),
    }
}
