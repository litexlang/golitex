use std::collections::{HashMap, HashSet};

use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, AndFact, AtomicFact, ChainFact, Fact, OrFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_quantifier_free_fact_rec(
        &mut self,
        fact: &QuantifierFreeFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<QuantifierFreeFact, InstError> {
        match fact {
            QuantifierFreeFact::AtomicFact(a) => Ok(QuantifierFreeFact::AtomicFact(
                self.inst_atomic_fact_rec(a, param_to_arg_map)?,
            )),
            QuantifierFreeFact::AndFact(a) => {
                let mut facts = Vec::with_capacity(a.facts.len());
                for f in &a.facts {
                    facts.push(self.inst_atomic_fact_rec(f, param_to_arg_map)?);
                }
                Ok(QuantifierFreeFact::AndFact(AndFact {
                    fact_id: self.ids.allocate_fact_id(),
                    facts,
                    line_file: a.line_file.clone(),
                }))
            }
            QuantifierFreeFact::ChainFact(c) => Ok(QuantifierFreeFact::ChainFact(
                self.inst_chain_fact(c, param_to_arg_map)?,
            )),
            QuantifierFreeFact::OrFact(o) => {
                let mut facts = Vec::with_capacity(o.facts.len());
                for f in &o.facts {
                    facts.push(self.inst_and_chain_atomic(f, param_to_arg_map)?);
                }
                Ok(QuantifierFreeFact::OrFact(OrFact {
                    fact_id: self.ids.allocate_fact_id(),
                    facts,
                    line_file: o.line_file.clone(),
                }))
            }
        }
    }

    pub(crate) fn inst_qf_facts_rec(
        &mut self,
        facts: &[QuantifierFreeFact],
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Vec<QuantifierFreeFact>, InstError> {
        let mut out = Vec::with_capacity(facts.len());
        for f in facts {
            out.push(self.inst_quantifier_free_fact_rec(
                f,
                param_to_arg_map,
            )?);
        }
        Ok(out)
    }

    fn inst_chain_fact(
        &mut self,
        fact: &ChainFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<ChainFact, InstError> {
        let mut objs = Vec::with_capacity(fact.objs.len());
        for o in &fact.objs {
            objs.push(self.inst_obj_rec(o, param_to_arg_map)?);
        }
        Ok(ChainFact {
            fact_id: self.ids.allocate_fact_id(),
            objs,
            prop_names: fact.prop_names.clone(),
            line_file: fact.line_file.clone(),
        })
    }

    pub(crate) fn inst_and_chain_atomic(
        &mut self,
        fact: &AndChainAtomicFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<AndChainAtomicFact, InstError> {
        match fact {
            AndChainAtomicFact::AtomicFact(a) => Ok(AndChainAtomicFact::AtomicFact(
                self.inst_atomic_fact_rec(a, param_to_arg_map)?,
            )),
            AndChainAtomicFact::AndFact(a) => {
                let mut facts = Vec::with_capacity(a.facts.len());
                for f in &a.facts {
                    facts.push(self.inst_atomic_fact_rec(f, param_to_arg_map)?);
                }
                Ok(AndChainAtomicFact::AndFact(AndFact {
                    fact_id: self.ids.allocate_fact_id(),
                    facts,
                    line_file: a.line_file.clone(),
                }))
            }
            AndChainAtomicFact::ChainFact(c) => Ok(AndChainAtomicFact::ChainFact(
                self.inst_chain_fact(c, param_to_arg_map)?,
            )),
        }
    }
}

pub fn quantifier_free_fact_to_fact(qf: QuantifierFreeFact) -> Fact {
    match qf {
        QuantifierFreeFact::AtomicFact(a) => Fact::AtomicFact(a),
        QuantifierFreeFact::AndFact(a) => Fact::AndFact(a),
        QuantifierFreeFact::ChainFact(c) => Fact::ChainFact(c),
        QuantifierFreeFact::OrFact(o) => Fact::OrFact(o),
    }
}

pub(crate) fn collect_free_plain_ids_in_qf_fact(
    fact: &QuantifierFreeFact,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => collect_free_plain_ids_in_atomic(a, bound, out),
        QuantifierFreeFact::AndFact(a) => {
            for f in &a.facts {
                collect_free_plain_ids_in_atomic(f, bound, out);
            }
        }
        QuantifierFreeFact::ChainFact(c) => {
            for o in &c.objs {
                super::super::capture::collect_free_plain_ids(o, bound, out);
            }
        }
        QuantifierFreeFact::OrFact(o) => {
            for f in &o.facts {
                collect_free_plain_ids_in_and_chain(f, bound, out);
            }
        }
    }
}

fn collect_free_plain_ids_in_and_chain(
    fact: &AndChainAtomicFact,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => collect_free_plain_ids_in_atomic(a, bound, out),
        AndChainAtomicFact::AndFact(a) => {
            for f in &a.facts {
                collect_free_plain_ids_in_atomic(f, bound, out);
            }
        }
        AndChainAtomicFact::ChainFact(c) => {
            for o in &c.objs {
                super::super::capture::collect_free_plain_ids(o, bound, out);
            }
        }
    }
}

fn collect_free_plain_ids_in_atomic(
    atomic: &AtomicFact,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    let args = atomic_fact_obj_args(atomic);
    for o in args {
        super::super::capture::collect_free_plain_ids(o, bound, out);
    }
}

fn atomic_fact_obj_args(atomic: &AtomicFact) -> Vec<&Obj> {
    match atomic {
        AtomicFact::NormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::NotNormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::EqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::LessFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::LessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::SubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::SupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::FnEqualInFact(f) => vec![&f.left, &f.right, &f.set],
        AtomicFact::NotFnEqualInFact(f) => vec![&f.left, &f.right, &f.set],
        AtomicFact::IsSetFact(f) => vec![&f.set],
        AtomicFact::NotIsSetFact(f) => vec![&f.set],
        AtomicFact::IsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::NotIsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::IsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::NotIsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::IsCartFact(f) => vec![&f.set],
        AtomicFact::NotIsCartFact(f) => vec![&f.set],
        AtomicFact::IsTupleFact(f) => vec![&f.set],
        AtomicFact::NotIsTupleFact(f) => vec![&f.set],
        AtomicFact::InFact(f) => vec![&f.element, &f.set],
        AtomicFact::NotInFact(f) => vec![&f.element, &f.set],
    }
}

pub fn collect_free_plain_ids_in_atomic_fact(
    atomic: &AtomicFact,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    collect_free_plain_ids_in_atomic(atomic, bound, out);
}

pub fn identifier_is_plain(name: &AtomicName) -> Option<&String> {
    if let AtomicName::Plain { name } = name {
        Some(name)
    } else {
        None
    }
}
