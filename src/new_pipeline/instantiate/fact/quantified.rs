use crate::new_pipeline::ast::fact::{
    ExistFact, ExistOrAndChainAtomicFact, Fact, ForallFact, ForallFactWithIff, NotForallFact,
    PlainExistFact,
};

use super::atomic;
use super::compound;
use super::super::InstCtx;
use super::super::capture;
use super::super::error::InstError;
use super::super::param;

pub fn inst_fact(ctx: &mut InstCtx<'_>, fact: &Fact) -> Result<Fact, InstError> {
    match fact {
        Fact::AtomicFact(a) => Ok(Fact::AtomicFact(atomic::inst_atomic_fact(ctx, a)?)),
        Fact::AndFact(a) => {
            let mut facts = Vec::with_capacity(a.facts.len());
            for f in &a.facts {
                facts.push(atomic::inst_atomic_fact(ctx, f)?);
            }
            Ok(Fact::AndFact(crate::new_pipeline::ast::fact::AndFact {
                fact_id: ctx.rt.ids.allocate_fact_id(),
                facts,
                line_file: a.line_file.clone(),
            }))
        }
        Fact::ChainFact(c) => {
            let mut objs = Vec::with_capacity(c.objs.len());
            for o in &c.objs {
                objs.push(ctx.inst_obj(o)?);
            }
            Ok(Fact::ChainFact(crate::new_pipeline::ast::fact::ChainFact {
                fact_id: ctx.rt.ids.allocate_fact_id(),
                objs,
                prop_names: c.prop_names.clone(),
                line_file: c.line_file.clone(),
            }))
        }
        Fact::OrFact(o) => {
            let mut facts = Vec::with_capacity(o.facts.len());
            for f in &o.facts {
                facts.push(compound::inst_and_chain_atomic(ctx, f)?);
            }
            Ok(Fact::OrFact(crate::new_pipeline::ast::fact::OrFact {
                fact_id: ctx.rt.ids.allocate_fact_id(),
                facts,
                line_file: o.line_file.clone(),
            }))
        }
        Fact::ExistFact(e) => Ok(Fact::ExistFact(inst_exist_fact(ctx, e)?)),
        Fact::ForallFact(f) => Ok(Fact::ForallFact(inst_forall_fact(ctx, f)?)),
        Fact::ForallFactWithIff(f) => Ok(Fact::ForallFactWithIff(inst_forall_fact_with_iff(
            ctx, f,
        )?)),
        Fact::NotForall(f) => Ok(Fact::NotForall(inst_not_forall_fact(ctx, f)?)),
    }
}

fn inst_plain_exist_fact_contents(
    ctx: &mut InstCtx<'_>,
    plain: &PlainExistFact,
) -> Result<PlainExistFact, InstError> {
    let typed_parameters = param::inst_typed_parameter_list(ctx, &plain.typed_parameters)?;
    let facts = compound::inst_qf_facts(ctx, &plain.facts)?;
    Ok(PlainExistFact {
        fact_id: ctx.rt.ids.allocate_fact_id(),
        typed_parameters,
        facts,
        line_file: plain.line_file.clone(),
    })
}

fn inst_plain_exist_fact(ctx: &mut InstCtx<'_>, plain: &PlainExistFact) -> Result<PlainExistFact, InstError> {
    let names = param::typed_param_names(&plain.typed_parameters);
    let binders = capture::prepare_binders(&names, &ctx.subst, &mut ctx.fresh_counter);
    capture::with_shadowed_binders(ctx, &binders, |ctx| inst_plain_exist_fact_contents(ctx, plain))
}

fn inst_exist_fact(ctx: &mut InstCtx<'_>, exist: &ExistFact) -> Result<ExistFact, InstError> {
    match exist {
        ExistFact::PlainExistFact(p) => Ok(ExistFact::PlainExistFact(inst_plain_exist_fact(ctx, p)?)),
        ExistFact::ExistUniqueFact(p) => {
            Ok(ExistFact::ExistUniqueFact(inst_plain_exist_fact(ctx, p)?))
        }
        ExistFact::NotExistFact(p) => Ok(ExistFact::NotExistFact(inst_plain_exist_fact(ctx, p)?)),
    }
}

fn inst_forall_fact_contents(ctx: &mut InstCtx<'_>, forall: &ForallFact) -> Result<ForallFact, InstError> {
    let typed_parameters = param::inst_typed_parameter_list(ctx, &forall.typed_parameters)?;
    let mut dom_facts = Vec::with_capacity(forall.dom_facts.len());
    for dom in &forall.dom_facts {
        dom_facts.push(inst_fact(ctx, dom)?);
    }
    let mut then_facts = Vec::with_capacity(forall.then_facts.len());
    for then in &forall.then_facts {
        then_facts.push(inst_exist_or_and_chain_atomic(ctx, then)?);
    }
    Ok(ForallFact {
        fact_id: ctx.rt.ids.allocate_fact_id(),
        typed_parameters,
        dom_facts,
        then_facts,
        line_file: forall.line_file.clone(),
    })
}

fn inst_forall_fact(ctx: &mut InstCtx<'_>, forall: &ForallFact) -> Result<ForallFact, InstError> {
    let names = param::typed_param_names(&forall.typed_parameters);
    let binders = capture::prepare_binders(&names, &ctx.subst, &mut ctx.fresh_counter);
    capture::with_shadowed_binders(ctx, &binders, |ctx| inst_forall_fact_contents(ctx, forall))
}

fn inst_forall_fact_with_iff(
    ctx: &mut InstCtx<'_>,
    f: &ForallFactWithIff,
) -> Result<ForallFactWithIff, InstError> {
    let names = param::typed_param_names(&f.forall_fact.typed_parameters);
    let binders = capture::prepare_binders(&names, &ctx.subst, &mut ctx.fresh_counter);
    capture::with_shadowed_binders(ctx, &binders, |ctx| {
        let forall_fact = inst_forall_fact_contents(ctx, &f.forall_fact)?;
        let mut iff_facts = Vec::with_capacity(f.iff_facts.len());
        for iff in &f.iff_facts {
            iff_facts.push(inst_exist_or_and_chain_atomic(ctx, iff)?);
        }
        Ok(ForallFactWithIff {
            fact_id: ctx.rt.ids.allocate_fact_id(),
            forall_fact,
            iff_facts,
            line_file: f.line_file.clone(),
        })
    })
}

fn inst_not_forall_fact(ctx: &mut InstCtx<'_>, f: &NotForallFact) -> Result<NotForallFact, InstError> {
    Ok(NotForallFact {
        fact_id: ctx.rt.ids.allocate_fact_id(),
        forall_fact: inst_forall_fact(ctx, &f.forall_fact)?,
    })
}

fn inst_exist_or_and_chain_atomic(
    ctx: &mut InstCtx<'_>,
    fact: &ExistOrAndChainAtomicFact,
) -> Result<ExistOrAndChainAtomicFact, InstError> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(a) => Ok(ExistOrAndChainAtomicFact::AtomicFact(
            atomic::inst_atomic_fact(ctx, a)?,
        )),
        ExistOrAndChainAtomicFact::AndFact(a) => {
            let mut facts = Vec::with_capacity(a.facts.len());
            for f in &a.facts {
                facts.push(atomic::inst_atomic_fact(ctx, f)?);
            }
            Ok(ExistOrAndChainAtomicFact::AndFact(
                crate::new_pipeline::ast::fact::AndFact {
                    fact_id: ctx.rt.ids.allocate_fact_id(),
                    facts,
                    line_file: a.line_file.clone(),
                },
            ))
        }
        ExistOrAndChainAtomicFact::ChainFact(c) => {
            let mut objs = Vec::with_capacity(c.objs.len());
            for o in &c.objs {
                objs.push(ctx.inst_obj(o)?);
            }
            Ok(ExistOrAndChainAtomicFact::ChainFact(
                crate::new_pipeline::ast::fact::ChainFact {
                    fact_id: ctx.rt.ids.allocate_fact_id(),
                    objs,
                    prop_names: c.prop_names.clone(),
                    line_file: c.line_file.clone(),
                },
            ))
        }
        ExistOrAndChainAtomicFact::OrFact(o) => {
            let mut facts = Vec::with_capacity(o.facts.len());
            for f in &o.facts {
                facts.push(compound::inst_and_chain_atomic(ctx, f)?);
            }
            Ok(ExistOrAndChainAtomicFact::OrFact(
                crate::new_pipeline::ast::fact::OrFact {
                    fact_id: ctx.rt.ids.allocate_fact_id(),
                    facts,
                    line_file: o.line_file.clone(),
                },
            ))
        }
        ExistOrAndChainAtomicFact::ExistFact(e) => Ok(ExistOrAndChainAtomicFact::ExistFact(
            inst_exist_fact(ctx, e)?,
        )),
    }
}
