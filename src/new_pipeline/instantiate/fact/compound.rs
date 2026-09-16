use std::collections::HashSet;

use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, AndFact, AtomicFact, ChainFact, Fact, OrFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;

use super::atomic;
use super::super::InstCtx;
use super::super::error::InstError;

pub fn inst_quantifier_free_fact(
    ctx: &mut InstCtx<'_>,
    fact: &QuantifierFreeFact,
) -> Result<QuantifierFreeFact, InstError> {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => Ok(QuantifierFreeFact::AtomicFact(
            atomic::inst_atomic_fact(ctx, a)?,
        )),
        QuantifierFreeFact::AndFact(a) => {
            let mut facts = Vec::with_capacity(a.facts.len());
            for f in &a.facts {
                facts.push(atomic::inst_atomic_fact(ctx, f)?);
            }
            Ok(QuantifierFreeFact::AndFact(AndFact {
                fact_id: ctx.rt.ids.allocate_fact_id(),
                facts,
                line_file: a.line_file.clone(),
            }))
        }
        QuantifierFreeFact::ChainFact(c) => Ok(QuantifierFreeFact::ChainFact(inst_chain_fact(
            ctx, c,
        )?)),
        QuantifierFreeFact::OrFact(o) => {
            let mut facts = Vec::with_capacity(o.facts.len());
            for f in &o.facts {
                facts.push(inst_and_chain_atomic(ctx, f)?);
            }
            Ok(QuantifierFreeFact::OrFact(OrFact {
                fact_id: ctx.rt.ids.allocate_fact_id(),
                facts,
                line_file: o.line_file.clone(),
            }))
        }
    }
}

pub(crate) fn inst_qf_facts(
    ctx: &mut InstCtx<'_>,
    facts: &[QuantifierFreeFact],
) -> Result<Vec<QuantifierFreeFact>, InstError> {
    let mut out = Vec::with_capacity(facts.len());
    for f in facts {
        out.push(inst_quantifier_free_fact(ctx, f)?);
    }
    Ok(out)
}

fn inst_chain_fact(ctx: &mut InstCtx<'_>, fact: &ChainFact) -> Result<ChainFact, InstError> {
    let mut objs = Vec::with_capacity(fact.objs.len());
    for o in &fact.objs {
        objs.push(ctx.inst_obj(o)?);
    }
    Ok(ChainFact {
        fact_id: ctx.rt.ids.allocate_fact_id(),
        objs,
        prop_names: fact.prop_names.clone(),
        line_file: fact.line_file.clone(),
    })
}

pub(crate) fn inst_and_chain_atomic(
    ctx: &mut InstCtx<'_>,
    fact: &AndChainAtomicFact,
) -> Result<AndChainAtomicFact, InstError> {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => Ok(AndChainAtomicFact::AtomicFact(
            atomic::inst_atomic_fact(ctx, a)?,
        )),
        AndChainAtomicFact::AndFact(a) => {
            let mut facts = Vec::with_capacity(a.facts.len());
            for f in &a.facts {
                facts.push(atomic::inst_atomic_fact(ctx, f)?);
            }
            Ok(AndChainAtomicFact::AndFact(AndFact {
                fact_id: ctx.rt.ids.allocate_fact_id(),
                facts,
                line_file: a.line_file.clone(),
            }))
        }
        AndChainAtomicFact::ChainFact(c) => Ok(AndChainAtomicFact::ChainFact(inst_chain_fact(
            ctx, c,
        )?)),
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

pub(crate) fn collect_free_plain_names_in_qf_fact(
    fact: &QuantifierFreeFact,
    bound: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => collect_free_plain_names_in_atomic(a, bound, out),
        QuantifierFreeFact::AndFact(a) => {
            for f in &a.facts {
                collect_free_plain_names_in_atomic(f, bound, out);
            }
        }
        QuantifierFreeFact::ChainFact(c) => {
            for o in &c.objs {
                super::super::capture::collect_free_plain_names(o, bound, out);
            }
        }
        QuantifierFreeFact::OrFact(o) => {
            for f in &o.facts {
                collect_free_plain_names_in_and_chain(f, bound, out);
            }
        }
    }
}

fn collect_free_plain_names_in_and_chain(
    fact: &AndChainAtomicFact,
    bound: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => collect_free_plain_names_in_atomic(a, bound, out),
        AndChainAtomicFact::AndFact(a) => {
            for f in &a.facts {
                collect_free_plain_names_in_atomic(f, bound, out);
            }
        }
        AndChainAtomicFact::ChainFact(c) => {
            for o in &c.objs {
                super::super::capture::collect_free_plain_names(o, bound, out);
            }
        }
    }
}

fn collect_free_plain_names_in_atomic(
    atomic: &AtomicFact,
    bound: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    let args = atomic_fact_obj_args(atomic);
    for o in args {
        super::super::capture::collect_free_plain_names(o, bound, out);
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
        AtomicFact::FnEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::FnEqualInFact(f) => vec![&f.left, &f.right, &f.set],
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

pub fn collect_free_plain_names_in_atomic_fact(
    atomic: &AtomicFact,
    bound: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    collect_free_plain_names_in_atomic(atomic, bound, out);
}

pub fn identifier_is_plain(name: &AtomicName) -> Option<&String> {
    if let AtomicName::Plain { name } = name {
        Some(name)
    } else {
        None
    }
}
