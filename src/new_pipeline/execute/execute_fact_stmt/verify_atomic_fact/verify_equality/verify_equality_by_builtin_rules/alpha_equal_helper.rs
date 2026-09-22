use std::collections::HashMap;
use std::mem::discriminant;

use crate::new_pipeline::ast::fact::{
    atomic_fact_args_ref, AndChainAtomicFact, AndFact, AtomicFact, ChainFact, OrFact,
    QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{
    AnonymousFn, FnObj, FnObjHead, FnSet, IdentifierObj, IntervalObj, Obj,
    OneSideInfinityIntervalObj, SetBuilder,
};
use crate::new_pipeline::ast::param::SetBoundParameterList;
use crate::new_pipeline::exec_env::KnownEqualToObjWithFreeParamsShape;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

// Structural alpha-equality for FnSet / SetBuilder (and nested objs/facts).
// Bound IdentifierIds may differ; free ids and non-binder structure must match.
// FactId is ignored.

pub fn fn_sets_alpha_equal(left: &FnSet, right: &FnSet) -> bool {
    fn_sets_alpha_equal_under(left, right, &HashMap::new())
}

pub fn set_builders_alpha_equal(left: &SetBuilder, right: &SetBuilder) -> bool {
    set_builders_alpha_equal_under(left, right, &HashMap::new())
}

pub fn anonymous_fns_alpha_equal(left: &AnonymousFn, right: &AnonymousFn) -> bool {
    anonymous_fns_alpha_equal_under(left, right, &HashMap::new())
}

fn fn_sets_alpha_equal_under(
    left: &FnSet,
    right: &FnSet,
    outer: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    let mut map = outer.clone();
    if !set_bound_params_alpha_equal(&left.set_bound_parameters, &right.set_bound_parameters, &mut map)
    {
        return false;
    }
    if left.dom_facts.len() != right.dom_facts.len() {
        return false;
    }
    for (lf, rf) in left.dom_facts.iter().zip(right.dom_facts.iter()) {
        if !quantifier_free_facts_alpha_equal(lf, rf, &map) {
            return false;
        }
    }
    objs_alpha_equal(left.ret_set.as_ref(), right.ret_set.as_ref(), &map)
}

fn set_builders_alpha_equal_under(
    left: &SetBuilder,
    right: &SetBuilder,
    outer: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    if !objs_alpha_equal(left.param_set.as_ref(), right.param_set.as_ref(), outer) {
        return false;
    }
    let mut map = outer.clone();
    if !extend_binder_map(&mut map, &left.param_binding, &right.param_binding) {
        return false;
    }
    if left.facts.len() != right.facts.len() {
        return false;
    }
    left.facts
        .iter()
        .zip(right.facts.iter())
        .all(|(lf, rf)| quantifier_free_facts_alpha_equal(lf, rf, &map))
}

fn set_bound_params_alpha_equal(
    left: &SetBoundParameterList,
    right: &SetBoundParameterList,
    map: &mut HashMap<IdentifierId, IdentifierId>,
) -> bool {
    if left.groups.len() != right.groups.len() {
        return false;
    }
    for (lg, rg) in left.groups.iter().zip(right.groups.iter()) {
        if lg.params.len() != rg.params.len() {
            return false;
        }
        if !objs_alpha_equal(lg.param_type.as_ref(), rg.param_type.as_ref(), map) {
            return false;
        }
        for (lp, rp) in lg.params.iter().zip(rg.params.iter()) {
            if !extend_binder_map(map, lp, rp) {
                return false;
            }
        }
    }
    true
}

fn extend_binder_map(
    map: &mut HashMap<IdentifierId, IdentifierId>,
    left: &BoundName,
    right: &BoundName,
) -> bool {
    if map.values().any(|id| *id == right.id) {
        return false;
    }
    map.insert(left.id, right.id);
    true
}

fn plain_ids_alpha_equal(
    left: IdentifierId,
    right: IdentifierId,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    if let Some(mapped) = map.get(&left) {
        return *mapped == right;
    }
    left == right && map.values().all(|id| *id != right)
}

fn objs_alpha_equal(left: &Obj, right: &Obj, map: &HashMap<IdentifierId, IdentifierId>) -> bool {
    match (left, right) {
        (Obj::Identifier(l), Obj::Identifier(r)) => identifier_objs_alpha_equal(l, r, map),
        (Obj::FnSet(l), Obj::FnSet(r)) => fn_sets_alpha_equal_under(l, r, map),
        (Obj::SetBuilder(l), Obj::SetBuilder(r)) => set_builders_alpha_equal_under(l, r, map),
        (Obj::AnonymousFn(l), Obj::AnonymousFn(r)) => anonymous_fns_alpha_equal_under(l, r, map),
        (Obj::FnObj(l), Obj::FnObj(r)) => fn_objs_alpha_equal(l, r, map),
        (Obj::Number(l), Obj::Number(r)) => l.normalized_value == r.normalized_value,
        (Obj::ImaginaryUnit(_), Obj::ImaginaryUnit(_)) => true,
        (Obj::EulerNumber(_), Obj::EulerNumber(_)) => true,
        (Obj::Pi(_), Obj::Pi(_)) => true,
        (Obj::Add(l), Obj::Add(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Sub(l), Obj::Sub(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Mul(l), Obj::Mul(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Div(l), Obj::Div(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Mod(l), Obj::Mod(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Quot(l), Obj::Quot(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Gcd(l), Obj::Gcd(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Lcm(l), Obj::Lcm(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Min(l), Obj::Min(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Max(l), Obj::Max(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Union(l), Obj::Union(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Intersect(l), Obj::Intersect(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::SetMinus(l), Obj::SetMinus(r)) => both(&l.left, &l.right, &r.left, &r.right, map),
        (Obj::Floor(l), Obj::Floor(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Ceil(l), Obj::Ceil(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Exp(l), Obj::Exp(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Ln(l), Obj::Ln(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Sign(l), Obj::Sign(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Factorial(l), Obj::Factorial(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Abs(l), Obj::Abs(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Sin(l), Obj::Sin(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Arcsin(l), Obj::Arcsin(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Arccos(l), Obj::Arccos(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Arctan(l), Obj::Arctan(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Arccot(l), Obj::Arccot(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Cos(l), Obj::Cos(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Tan(l), Obj::Tan(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Cot(l), Obj::Cot(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::RealPart(l), Obj::RealPart(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::ImaginaryPart(l), Obj::ImaginaryPart(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::ComplexAbs(l), Obj::ComplexAbs(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::Sqrt(l), Obj::Sqrt(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::BigUnion(l), Obj::BigUnion(r)) => objs_alpha_equal(&l.left, &r.left, map),
        (Obj::BigIntersect(l), Obj::BigIntersect(r)) => objs_alpha_equal(&l.left, &r.left, map),
        (Obj::Pow(l), Obj::Pow(r)) => {
            objs_alpha_equal(&l.base, &r.base, map) && objs_alpha_equal(&l.exponent, &r.exponent, map)
        }
        (Obj::Log(l), Obj::Log(r)) => {
            objs_alpha_equal(&l.base, &r.base, map) && objs_alpha_equal(&l.arg, &r.arg, map)
        }
        (Obj::IndexUnion(l), Obj::IndexUnion(r)) => {
            objs_alpha_equal(&l.index_set, &r.index_set, map)
                && objs_alpha_equal(&l.ambient_set, &r.ambient_set, map)
                && objs_alpha_equal(&l.family_fn, &r.family_fn, map)
        }
        (Obj::IndexIntersect(l), Obj::IndexIntersect(r)) => {
            objs_alpha_equal(&l.index_set, &r.index_set, map)
                && objs_alpha_equal(&l.ambient_set, &r.ambient_set, map)
                && objs_alpha_equal(&l.family_fn, &r.family_fn, map)
        }
        (Obj::PowerSet(l), Obj::PowerSet(r)) => objs_alpha_equal(&l.set, &r.set, map),
        (Obj::GeneralCart(l), Obj::GeneralCart(r)) => {
            objs_alpha_equal(&l.index_set, &r.index_set, map)
                && objs_alpha_equal(&l.family_set, &r.family_set, map)
                && objs_alpha_equal(&l.family_fn, &r.family_fn, map)
        }
        (Obj::ListSet(l), Obj::ListSet(r)) => boxes_alpha_equal(&l.list, &r.list, map),
        (Obj::Cart(l), Obj::Cart(r)) => boxes_alpha_equal(&l.args, &r.args, map),
        (Obj::Tuple(l), Obj::Tuple(r)) => boxes_alpha_equal(&l.args, &r.args, map),
        (Obj::CartDim(l), Obj::CartDim(r)) => objs_alpha_equal(&l.set, &r.set, map),
        (Obj::FiniteSetSize(l), Obj::FiniteSetSize(r)) => objs_alpha_equal(&l.set, &r.set, map),
        (Obj::FiniteSetMax(l), Obj::FiniteSetMax(r)) => objs_alpha_equal(&l.set, &r.set, map),
        (Obj::FiniteSetMin(l), Obj::FiniteSetMin(r)) => objs_alpha_equal(&l.set, &r.set, map),
        (Obj::SeqSet(l), Obj::SeqSet(r)) => objs_alpha_equal(&l.set, &r.set, map),
        (Obj::Proj(l), Obj::Proj(r)) => {
            objs_alpha_equal(&l.set, &r.set, map) && objs_alpha_equal(&l.dim, &r.dim, map)
        }
        (Obj::TupleDim(l), Obj::TupleDim(r)) => objs_alpha_equal(&l.arg, &r.arg, map),
        (Obj::FnRange(l), Obj::FnRange(r)) => objs_alpha_equal(&l.function, &r.function, map),
        (Obj::Replacement(l), Obj::Replacement(r)) => {
            l.prop_name == r.prop_name && objs_alpha_equal(&l.source_set, &r.source_set, map)
        }
        (Obj::Sum(l), Obj::Sum(r)) => {
            objs_alpha_equal(&l.start, &r.start, map)
                && objs_alpha_equal(&l.end, &r.end, map)
                && objs_alpha_equal(&l.func, &r.func, map)
        }
        (Obj::Product(l), Obj::Product(r)) => {
            objs_alpha_equal(&l.start, &r.start, map)
                && objs_alpha_equal(&l.end, &r.end, map)
                && objs_alpha_equal(&l.func, &r.func, map)
        }
        (Obj::SumOfFiniteSet(l), Obj::SumOfFiniteSet(r)) => {
            objs_alpha_equal(&l.set, &r.set, map) && objs_alpha_equal(&l.func, &r.func, map)
        }
        (Obj::ProductOfFiniteSet(l), Obj::ProductOfFiniteSet(r)) => {
            objs_alpha_equal(&l.set, &r.set, map) && objs_alpha_equal(&l.func, &r.func, map)
        }
        (Obj::Reduce(l), Obj::Reduce(r)) => {
            objs_alpha_equal(&l.start, &r.start, map)
                && objs_alpha_equal(&l.end, &r.end, map)
                && objs_alpha_equal(&l.func, &r.func, map)
                && objs_alpha_equal(&l.op, &r.op, map)
                && objs_alpha_equal(&l.seed, &r.seed, map)
        }
        (Obj::FiniteSetReduce(l), Obj::FiniteSetReduce(r)) => {
            objs_alpha_equal(&l.set, &r.set, map)
                && objs_alpha_equal(&l.func, &r.func, map)
                && objs_alpha_equal(&l.op, &r.op, map)
                && objs_alpha_equal(&l.seed, &r.seed, map)
        }
        (Obj::Range(l), Obj::Range(r)) => {
            objs_alpha_equal(&l.start, &r.start, map) && objs_alpha_equal(&l.end, &r.end, map)
        }
        (Obj::ClosedRange(l), Obj::ClosedRange(r)) => {
            objs_alpha_equal(&l.start, &r.start, map) && objs_alpha_equal(&l.end, &r.end, map)
        }
        (Obj::FiniteSeqSet(l), Obj::FiniteSeqSet(r)) => {
            objs_alpha_equal(&l.set, &r.set, map) && objs_alpha_equal(&l.n, &r.n, map)
        }
        (Obj::ObjAtIndex(l), Obj::ObjAtIndex(r)) => {
            objs_alpha_equal(&l.obj, &r.obj, map) && objs_alpha_equal(&l.index, &r.index, map)
        }
        (Obj::StandardSet(l), Obj::StandardSet(r)) => l == r,
        (Obj::StructObj(l), Obj::StructObj(r)) => {
            l.name == r.name && objs_slice_alpha_equal(&l.params, &r.params, map)
        }
        (Obj::FieldAccess(l), Obj::FieldAccess(r)) => {
            l.fields == r.fields && objs_alpha_equal(l.obj.as_ref(), r.obj.as_ref(), map)
        }
        (Obj::InstantiatedTemplateObj(l), Obj::InstantiatedTemplateObj(r)) => {
            l.template_name == r.template_name && objs_slice_alpha_equal(&l.args, &r.args, map)
        }
        (Obj::OneSideInfinityIntervalObj(l), Obj::OneSideInfinityIntervalObj(r)) => {
            one_side_intervals_alpha_equal(l, r, map)
        }
        (Obj::IntervalObj(l), Obj::IntervalObj(r)) => intervals_alpha_equal(l, r, map),
        _ => false,
    }
}

fn both(
    a0: &Obj,
    a1: &Obj,
    b0: &Obj,
    b1: &Obj,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    objs_alpha_equal(a0, b0, map) && objs_alpha_equal(a1, b1, map)
}

fn identifier_objs_alpha_equal(
    left: &IdentifierObj,
    right: &IdentifierObj,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    match (left, right) {
        (IdentifierObj::Plain { id: lid, .. }, IdentifierObj::Plain { id: rid, .. }) => {
            plain_ids_alpha_equal(*lid, *rid, map)
        }
        (
            IdentifierObj::WithExportFileId {
                export_file_id: le,
                name: ln,
            },
            IdentifierObj::WithExportFileId {
                export_file_id: re,
                name: rn,
            },
        ) => le == re && ln == rn,
        (
            IdentifierObj::WithModAndExportFileId {
                global_mod_id: lm,
                export_file_id: le,
                name: ln,
            },
            IdentifierObj::WithModAndExportFileId {
                global_mod_id: rm,
                export_file_id: re,
                name: rn,
            },
        ) => lm == rm && le == re && ln == rn,
        _ => false,
    }
}

fn anonymous_fns_alpha_equal_under(
    left: &AnonymousFn,
    right: &AnonymousFn,
    outer: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    // Binders of the FnSet body also scope over equal_to.
    let mut map = outer.clone();
    if !set_bound_params_alpha_equal(
        &left.body.set_bound_parameters,
        &right.body.set_bound_parameters,
        &mut map,
    ) {
        return false;
    }
    if left.body.dom_facts.len() != right.body.dom_facts.len() {
        return false;
    }
    for (lf, rf) in left.body.dom_facts.iter().zip(right.body.dom_facts.iter()) {
        if !quantifier_free_facts_alpha_equal(lf, rf, &map) {
            return false;
        }
    }
    if !objs_alpha_equal(left.body.ret_set.as_ref(), right.body.ret_set.as_ref(), &map) {
        return false;
    }
    objs_alpha_equal(left.equal_to.as_ref(), right.equal_to.as_ref(), &map)
}

fn fn_objs_alpha_equal(left: &FnObj, right: &FnObj, map: &HashMap<IdentifierId, IdentifierId>) -> bool {
    if !fn_obj_heads_alpha_equal(left.head.as_ref(), right.head.as_ref(), map) {
        return false;
    }
    if left.body.len() != right.body.len() {
        return false;
    }
    left.body
        .iter()
        .zip(right.body.iter())
        .all(|(lg, rg)| boxes_alpha_equal(lg, rg, map))
}

fn fn_obj_heads_alpha_equal(
    left: &FnObjHead,
    right: &FnObjHead,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    match (left, right) {
        (FnObjHead::Identifier(l), FnObjHead::Identifier(r)) => {
            identifier_objs_alpha_equal(l, r, map)
        }
        (FnObjHead::AnonymousFnLiteral(l), FnObjHead::AnonymousFnLiteral(r)) => {
            anonymous_fns_alpha_equal_under(l, r, map)
        }
        (FnObjHead::FieldAccess(l), FnObjHead::FieldAccess(r)) => {
            l.fields == r.fields && objs_alpha_equal(l.obj.as_ref(), r.obj.as_ref(), map)
        }
        (FnObjHead::InstantiatedTemplateObj(l), FnObjHead::InstantiatedTemplateObj(r)) => {
            l.template_name == r.template_name && objs_slice_alpha_equal(&l.args, &r.args, map)
        }
        _ => false,
    }
}

fn one_side_intervals_alpha_equal(
    left: &OneSideInfinityIntervalObj,
    right: &OneSideInfinityIntervalObj,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    match (left, right) {
        (OneSideInfinityIntervalObj::LeftOpen(l), OneSideInfinityIntervalObj::LeftOpen(r))
        | (OneSideInfinityIntervalObj::LeftClosed(l), OneSideInfinityIntervalObj::LeftClosed(r))
        | (OneSideInfinityIntervalObj::RightOpen(l), OneSideInfinityIntervalObj::RightOpen(r))
        | (OneSideInfinityIntervalObj::RightClosed(l), OneSideInfinityIntervalObj::RightClosed(r)) => {
            objs_alpha_equal(l.start.as_ref(), r.start.as_ref(), map)
        }
        _ => false,
    }
}

fn intervals_alpha_equal(
    left: &IntervalObj,
    right: &IntervalObj,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    match (left, right) {
        (IntervalObj::LeftOpenRightOpen(l), IntervalObj::LeftOpenRightOpen(r))
        | (IntervalObj::LeftOpenRightClosed(l), IntervalObj::LeftOpenRightClosed(r))
        | (IntervalObj::LeftClosedRightOpen(l), IntervalObj::LeftClosedRightOpen(r))
        | (IntervalObj::LeftClosedRightClosed(l), IntervalObj::LeftClosedRightClosed(r)) => {
            objs_alpha_equal(l.start.as_ref(), r.start.as_ref(), map)
                && objs_alpha_equal(l.end.as_ref(), r.end.as_ref(), map)
        }
        _ => false,
    }
}

fn boxes_alpha_equal(
    left: &[Box<Obj>],
    right: &[Box<Obj>],
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right.iter())
            .all(|(l, r)| objs_alpha_equal(l, r, map))
}

fn objs_slice_alpha_equal(
    left: &[Obj],
    right: &[Obj],
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right.iter())
            .all(|(l, r)| objs_alpha_equal(l, r, map))
}

fn quantifier_free_facts_alpha_equal(
    left: &QuantifierFreeFact,
    right: &QuantifierFreeFact,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    match (left, right) {
        (QuantifierFreeFact::AtomicFact(l), QuantifierFreeFact::AtomicFact(r)) => {
            atomic_facts_alpha_equal(l, r, map)
        }
        (QuantifierFreeFact::AndFact(l), QuantifierFreeFact::AndFact(r)) => {
            and_facts_alpha_equal(l, r, map)
        }
        (QuantifierFreeFact::ChainFact(l), QuantifierFreeFact::ChainFact(r)) => {
            chain_facts_alpha_equal(l, r, map)
        }
        (QuantifierFreeFact::OrFact(l), QuantifierFreeFact::OrFact(r)) => {
            or_facts_alpha_equal(l, r, map)
        }
        _ => false,
    }
}

fn and_facts_alpha_equal(
    left: &AndFact,
    right: &AndFact,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    left.facts.len() == right.facts.len()
        && left
            .facts
            .iter()
            .zip(right.facts.iter())
            .all(|(l, r)| atomic_facts_alpha_equal(l, r, map))
}

fn chain_facts_alpha_equal(
    left: &ChainFact,
    right: &ChainFact,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    left.prop_names == right.prop_names && objs_slice_alpha_equal(&left.objs, &right.objs, map)
}

fn or_facts_alpha_equal(
    left: &OrFact,
    right: &OrFact,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    left.facts.len() == right.facts.len()
        && left
            .facts
            .iter()
            .zip(right.facts.iter())
            .all(|(l, r)| and_chain_atomic_facts_alpha_equal(l, r, map))
}

fn and_chain_atomic_facts_alpha_equal(
    left: &AndChainAtomicFact,
    right: &AndChainAtomicFact,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    match (left, right) {
        (AndChainAtomicFact::AtomicFact(l), AndChainAtomicFact::AtomicFact(r)) => {
            atomic_facts_alpha_equal(l, r, map)
        }
        (AndChainAtomicFact::AndFact(l), AndChainAtomicFact::AndFact(r)) => {
            and_facts_alpha_equal(l, r, map)
        }
        (AndChainAtomicFact::ChainFact(l), AndChainAtomicFact::ChainFact(r)) => {
            chain_facts_alpha_equal(l, r, map)
        }
        _ => false,
    }
}

fn atomic_facts_alpha_equal(
    left: &AtomicFact,
    right: &AtomicFact,
    map: &HashMap<IdentifierId, IdentifierId>,
) -> bool {
    if discriminant(left) != discriminant(right) {
        return false;
    }
    match (left, right) {
        (AtomicFact::NormalAtomicFact(l), AtomicFact::NormalAtomicFact(r)) => {
            if l.predicate != r.predicate {
                return false;
            }
        }
        (AtomicFact::NotNormalAtomicFact(l), AtomicFact::NotNormalAtomicFact(r)) => {
            if l.predicate != r.predicate {
                return false;
            }
        }
        _ => {}
    }
    let left_args = atomic_fact_args_ref(left);
    let right_args = atomic_fact_args_ref(right);
    left_args.len() == right_args.len()
        && left_args
            .iter()
            .zip(right_args.iter())
            .all(|(l, r)| objs_alpha_equal(l, r, map))
}

pub fn free_params_shapes_alpha_equal(
    left: &KnownEqualToObjWithFreeParamsShape,
    right: &KnownEqualToObjWithFreeParamsShape,
) -> bool {
    match (left, right) {
        (
            KnownEqualToObjWithFreeParamsShape::FnSet(l),
            KnownEqualToObjWithFreeParamsShape::FnSet(r),
        ) => fn_sets_alpha_equal(l, r),
        (
            KnownEqualToObjWithFreeParamsShape::AnonymousFn(l),
            KnownEqualToObjWithFreeParamsShape::AnonymousFn(r),
        ) => anonymous_fns_alpha_equal_under(l, r, &HashMap::new()),
        (
            KnownEqualToObjWithFreeParamsShape::SetBuilder(l),
            KnownEqualToObjWithFreeParamsShape::SetBuilder(r),
        ) => set_builders_alpha_equal(l, r),
        _ => false,
    }
}

