//! Finite sum order, substitution and reindexing contracts.
use super::helper::*;
use crate::ast::fact::Fact;
use crate::ast::obj::*;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

pub(super) fn prepare_sums(rt: &mut Runtime, id: BuiltinTheoremId, args: &[Obj]) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    let result = prepare_sums_contract(rt, id, args);
    Ok(result)
}

fn prepare_sums_contract(rt: &mut Runtime, id: BuiltinTheoremId, args: &[Obj]) -> Result<(Vec<Fact>, Vec<Fact>), String> {
    use BuiltinTheoremId::*;
    let a = args[0].clone();
    let b = args[1].clone();
    let conclusion = if matches!(id, FiniteSetSumSubstitution | SumOverBijectiveFiniteSetEnumerations) { equal(rt, a.clone(), b.clone()) } else { le(rt, a.clone(), b.clone()) };
    let requirements = match id {
        SumLessEqualFromPointwise => {
            let (Obj::IteratedOperator(IteratedOperator::Sum(left)), Obj::IteratedOperator(IteratedOperator::Sum(right))) = (&a, &b) else { return Err("both arguments must be sum(...) objects".to_string()); };
            let i = rt.fresh_internal_param();
            let domain = unary_domain(&left.func).or_else(|| unary_domain(&right.func)).unwrap_or(Obj::StandardSet(StandardSet::Z));
            let left_value = apply_body(rt, &left.func, identifier(&i))?;
            let right_value = apply_body(rt, &right.func, identifier(&i))?;
            let body = le(rt, left_value, right_value);
            let dom = vec![le(rt, left.start.as_ref().clone(), identifier(&i)).into(), le(rt, identifier(&i), left.end.as_ref().clone()).into()];
            vec![equal(rt, left.start.as_ref().clone(), right.start.as_ref().clone()).into(), equal(rt, left.end.as_ref().clone(), right.end.as_ref().clone()).into(), forall(rt, i, domain, dom, vec![body])]
        }
        FiniteSetSumLessEqualFromPointwise => {
            let (left, right) = finite_sums(&a, &b)?;
            let x = rt.fresh_internal_param();
            let l = apply_body(rt, &left.func, identifier(&x))?;
            let r = apply_body(rt, &right.func, identifier(&x))?;
            let body = le(rt, l, r);
            vec![equal(rt, left.set.as_ref().clone(), right.set.as_ref().clone()).into(), forall(rt, x, left.set.as_ref().clone(), vec![], vec![body])]
        }
        FiniteSetSummandLessEqualSum => {
            let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = &b else { return Err("second argument must be finite_set_sum(...)".to_string()); };
            let Obj::FnObj(call) = &a else { return Err("first argument must be a unary summand application".to_string()); };
            let Some(member) = unary_argument(call) else { return Err("first argument must be a unary summand application".to_string()); };
            let value = apply_body(rt, &sum.func, member.clone())?;
            let x = rt.fresh_internal_param();
            let value_at_x = apply_body(rt, &sum.func, identifier(&x))?;
            let body = le(rt, number("0"), value_at_x);
            vec![equal(rt, a.clone(), value).into(), atomic_in(rt, member, sum.set.as_ref().clone()).into(), forall(rt, x, sum.set.as_ref().clone(), vec![], vec![body])]
        }
        FiniteSetSumSubstitution => {
            let (left, right) = finite_sums(&a, &b)?;
            // A syntactic pullback f(g(y)) selects reindexing; otherwise use
            // pointwise equality on a common finite set.
            let mut substitution = None;
            for (source, pullback) in [(&left, &right), (&right, &left)] {
                let y = rt.fresh_internal_param();
                let value = apply_body(rt, &pullback.func, identifier(&y))?;
                if let Some(map) = pullback_map(&value, &source.func, &identifier(&y)) {
                    let mapped = apply_body(rt, &map, identifier(&y))?;
                    let source_value = apply_body(rt, &source.func, mapped)?;
                    let body = equal(rt, value, source_value);
                    substitution = Some(vec![
                        bijective(rt, pullback.set.as_ref().clone(), source.set.as_ref().clone(), map).into(),
                        forall(rt, y, pullback.set.as_ref().clone(), vec![], vec![body]),
                    ]);
                    break;
                }
            }
            if let Some(requirements) = substitution { requirements } else {
                let x = rt.fresh_internal_param();
                let l = apply_body(rt, &left.func, identifier(&x))?;
                let r = apply_body(rt, &right.func, identifier(&x))?;
                let body = equal(rt, l, r);
                vec![equal(rt, left.set.as_ref().clone(), right.set.as_ref().clone()).into(), forall(rt, x, left.set.as_ref().clone(), vec![], vec![body])]
            }
        }
        SumOverBijectiveFiniteSetEnumerations => {
            let (Obj::IteratedOperator(IteratedOperator::Sum(left)), Obj::IteratedOperator(IteratedOperator::Sum(right))) = (&a, &b) else { return Err("both arguments must be sum(...) objects".to_string()); };
            let i = rt.fresh_internal_param();
            let left_value = apply_body(rt, &left.func, identifier(&i))?;
            let right_value = apply_body(rt, &right.func, identifier(&i))?;
            let (left_outer, left_enum) = enumeration(&left_value, &identifier(&i))?;
            let (right_outer, right_enum) = enumeration(&right_value, &identifier(&i))?;
            let left_target = return_set(rt, &left_enum).ok_or("cannot recover left enumerator's codomain")?;
            let right_target = return_set(rt, &right_enum).ok_or("cannot recover right enumerator's codomain")?;
            let domain = range(left.start.as_ref().clone(), left.end.as_ref().clone());
            vec![equal(rt, left.start.as_ref().clone(), right.start.as_ref().clone()).into(), equal(rt, left.end.as_ref().clone(), right.end.as_ref().clone()).into(), equal(rt, left_outer, right_outer).into(), equal(rt, left_target.clone(), right_target).into(), finite(rt, left_target.clone()).into(), bijective(rt, domain.clone(), left_target.clone(), left_enum).into(), bijective(rt, domain, left_target, right_enum).into()]
        }
        _ => unreachable!(),
    };
    Ok((requirements, vec![conclusion.into()]))
}
fn finite_sums(a: &Obj, b: &Obj) -> Result<(SumOfFiniteSet, SumOfFiniteSet), String> {
    match (a, b) {
        (Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(l)), Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(r))) => Ok((l.clone(), r.clone())),
        _ => Err("both arguments must be finite_set_sum(...) objects".to_string()),
    }
}
fn unary_domain(function: &Obj) -> Option<Obj> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = function else { return None; };
    let [group] = anon.body.set_bound_parameters.groups.as_slice() else { return None; };
    if group.params.len() != 1 { return None; }
    Some(group.param_type.as_ref().clone())
}
fn apply_body(rt: &mut Runtime, function: &Obj, arg: Obj) -> Result<Obj, String> {
    if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = function {
        let [group] = anon.body.set_bound_parameters.groups.as_slice() else { return Err("expected unary anonymous function".to_string()); };
        let [param] = group.params.as_slice() else { return Err("expected unary anonymous function".to_string()); };
        let mut subst = HashMap::new();
        subst.insert(param.id, arg);
        return rt.inst_obj(&anon.equal_to, &subst).map_err(|error| error.to_string());
    }
    apply(function, vec![arg])
}
fn head_obj(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(x) => Obj::Identifier(x.clone()),
        FnObjHead::AnonymousFnLiteral(x) => Obj::FunctionSpace(FunctionSpace::AnonymousFn(x.as_ref().clone())),
        FnObjHead::FieldAccess(x) => Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(x.clone())),
        FnObjHead::InstantiatedTemplateObj(x) => Obj::InstantiatedTemplateObj(x.clone()),
    }
}
fn unary_argument(call: &FnObj) -> Option<Obj> {
    let [group] = call.body.as_slice() else { return None; };
    let [arg] = group.as_slice() else { return None; };
    Some(arg.as_ref().clone())
}
fn pullback_map(value: &Obj, source: &Obj, param: &Obj) -> Option<Obj> {
    let Obj::FnObj(outer) = value else { return None; };
    if head_obj(&outer.head) != *source { return None; }
    let Obj::FnObj(inner) = unary_argument(outer)? else { return None; };
    if unary_argument(&inner)? != *param { return None; }
    Some(head_obj(&inner.head))
}
fn enumeration(value: &Obj, param: &Obj) -> Result<(Obj, Obj), String> {
    let Obj::FnObj(outer) = value else { return Err("summands must have shape h(enumerator(i))".to_string()); };
    let source = head_obj(&outer.head);
    let map = pullback_map(value, &source, param).ok_or("summands must have shape h(enumerator(i))")?;
    Ok((source, map))
}
fn return_set(rt: &Runtime, function: &Obj) -> Option<Obj> {
    if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = function { return Some(anon.body.ret_set.as_ref().clone()); }
    rt.collect_in_function_set_candidates(function).first().map(|(fs, _)| fs.ret_set.as_ref().clone())
}
