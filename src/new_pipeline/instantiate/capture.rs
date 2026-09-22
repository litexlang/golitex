use std::collections::{HashMap, HashSet};

use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{
    AnonymousFn, ArithmeticOperator, ComplexOperator, ExpLogOperator, FiniteSetStat, FnSet,
    FunctionSpace, IdentifierObj, IntegerOperator, IteratedOperator, Literal, Obj, ProductShape,
    SetBuilder, SetFormer, SetOperator, StructAndFieldAccessObj, TrigOperator,
};
use crate::new_pipeline::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::Runtime;

use super::error::InstError;
use super::fact;

fn collect_unary(arg: &Obj, bound: &HashSet<IdentifierId>, out: &mut HashSet<IdentifierId>) {
    collect_free_plain_ids(arg, bound, out);
}

fn collect_obj_list(
    list: &[Box<Obj>],
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    for o in list {
        collect_free_plain_ids(o, bound, out);
    }
}

fn collect_binary(
    left: &Obj,
    right: &Obj,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    collect_free_plain_ids(left, bound, out);
    collect_free_plain_ids(right, bound, out);
}

fn collect_ternary(
    a: &Obj,
    b: &Obj,
    c: &Obj,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    collect_free_plain_ids(a, bound, out);
    collect_free_plain_ids(b, bound, out);
    collect_free_plain_ids(c, bound, out);
}

pub fn free_plain_ids_in_subst(subst: &HashMap<IdentifierId, Obj>) -> HashSet<IdentifierId> {
    let mut ids = HashSet::new();
    for obj in subst.values() {
        collect_free_plain_ids(obj, &HashSet::new(), &mut ids);
    }
    ids
}

pub fn collect_free_plain_ids(
    obj: &Obj,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    match obj {
        Obj::Identifier(id) => {
            if let IdentifierObj::Plain { id, .. } = id {
                if !bound.contains(id) {
                    out.insert(*id);
                }
            }
        }
        Obj::FnObj(f) => {
            match f.head.as_ref() {
                crate::new_pipeline::ast::obj::FnObjHead::Identifier(id) => {
                    collect_free_plain_ids(&Obj::Identifier(id.clone()), bound, out);
                }
                crate::new_pipeline::ast::obj::FnObjHead::AnonymousFnLiteral(af) => {
                    collect_free_in_anonymous_fn(af, bound, out);
                }
                crate::new_pipeline::ast::obj::FnObjHead::FieldAccess(a) => {
                    collect_free_plain_ids(&a.obj, bound, out);
                }
                crate::new_pipeline::ast::obj::FnObjHead::InstantiatedTemplateObj(a) => {
                    for o in &a.args {
                        collect_free_plain_ids(o, bound, out);
                    }
                }
            }
            for group in &f.body {
                for o in group {
                    collect_free_plain_ids(o, bound, out);
                }
            }
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::IntegerOperator(IntegerOperator::Mod(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::IntegerOperator(IntegerOperator::Quot(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::IntegerOperator(IntegerOperator::Gcd(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::IntegerOperator(IntegerOperator::Lcm(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Min(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Max(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => {
            collect_free_plain_ids(&a.base, bound, out);
            collect_free_plain_ids(&a.exponent, bound, out);
        }
        Obj::ExpLogOperator(ExpLogOperator::Log(a)) => {
            collect_free_plain_ids(&a.base, bound, out);
            collect_free_plain_ids(&a.arg, bound, out);
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(a)) => collect_unary(&a.arg, bound, out),
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(a)) => collect_unary(&a.arg, bound, out),
        Obj::ExpLogOperator(ExpLogOperator::Exp(a)) => collect_unary(&a.arg, bound, out),
        Obj::ExpLogOperator(ExpLogOperator::Ln(a)) => collect_unary(&a.arg, bound, out),
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(a)) => collect_unary(&a.arg, bound, out),
        Obj::IntegerOperator(IntegerOperator::Factorial(a)) => collect_unary(&a.arg, bound, out),
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Sin(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Arcsin(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Arccos(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Arctan(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Arccot(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Cos(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Tan(a)) => collect_unary(&a.arg, bound, out),
        Obj::TrigOperator(TrigOperator::Cot(a)) => collect_unary(&a.arg, bound, out),
        Obj::ComplexOperator(ComplexOperator::RealPart(a)) => collect_unary(&a.arg, bound, out),
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(a)) => {
            collect_unary(&a.arg, bound, out)
        }
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(a)) => collect_unary(&a.arg, bound, out),
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)) => collect_unary(&a.arg, bound, out),
        Obj::SetOperator(SetOperator::Union(a)) => collect_binary(&a.left, &a.right, bound, out),
        Obj::SetOperator(SetOperator::Intersect(a)) => {
            collect_binary(&a.left, &a.right, bound, out)
        }
        Obj::SetOperator(SetOperator::SetMinus(a)) => collect_binary(&a.left, &a.right, bound, out),
        Obj::SetOperator(SetOperator::FamilyUnion(a)) => {
            collect_free_plain_ids(&a.left, bound, out)
        }
        Obj::SetOperator(SetOperator::FamilyIntersect(a)) => {
            collect_free_plain_ids(&a.left, bound, out)
        }
        Obj::SetOperator(SetOperator::IndexUnion(a)) => {
            collect_free_plain_ids(&a.index_set, bound, out);
            collect_free_plain_ids(&a.ambient_set, bound, out);
            collect_free_plain_ids(&a.family_fn, bound, out);
        }
        Obj::SetOperator(SetOperator::IndexIntersect(a)) => {
            collect_free_plain_ids(&a.index_set, bound, out);
            collect_free_plain_ids(&a.ambient_set, bound, out);
            collect_free_plain_ids(&a.family_fn, bound, out);
        }
        Obj::SetOperator(SetOperator::PowerSet(a)) => collect_free_plain_ids(&a.set, bound, out),
        Obj::SetOperator(SetOperator::IndexCart(a)) => {
            collect_free_plain_ids(&a.index_set, bound, out);
            collect_free_plain_ids(&a.family_set, bound, out);
            collect_free_plain_ids(&a.family_fn, bound, out);
        }
        Obj::SetFormer(SetFormer::ListSet(a)) => {
            for o in &a.list {
                collect_free_plain_ids(o, bound, out);
            }
        }
        Obj::SetFormer(SetFormer::SetBuilder(sb)) => collect_free_in_set_builder(sb, bound, out),
        Obj::FunctionSpace(FunctionSpace::FnSet(fs)) => collect_free_in_fn_set(fs, bound, out),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => {
            collect_free_in_anonymous_fn(af, bound, out)
        }
        Obj::ProductShape(ProductShape::Cart(a)) => collect_obj_list(&a.args, bound, out),
        Obj::ProductShape(ProductShape::Tuple(a)) => collect_obj_list(&a.args, bound, out),
        Obj::ProductShape(ProductShape::CartDim(a)) => collect_free_plain_ids(&a.set, bound, out),
        Obj::ProductShape(ProductShape::Proj(a)) => {
            collect_free_plain_ids(&a.set, bound, out);
            collect_free_plain_ids(&a.dim, bound, out);
        }
        Obj::ProductShape(ProductShape::TupleDim(a)) => collect_free_plain_ids(&a.arg, bound, out),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(a)) => {
            collect_free_plain_ids(&a.set, bound, out)
        }
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(a)) => {
            collect_free_plain_ids(&a.set, bound, out)
        }
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(a)) => {
            collect_free_plain_ids(&a.set, bound, out)
        }
        Obj::FunctionSpace(FunctionSpace::FnRange(a)) => {
            collect_free_plain_ids(&a.function, bound, out)
        }
        Obj::IteratedOperator(IteratedOperator::Sum(a)) => {
            collect_ternary(&a.start, &a.end, &a.func, bound, out)
        }
        Obj::IteratedOperator(IteratedOperator::Product(a)) => {
            collect_ternary(&a.start, &a.end, &a.func, bound, out)
        }
        Obj::IteratedOperator(IteratedOperator::Reduce(a)) => {
            collect_free_plain_ids(&a.start, bound, out);
            collect_free_plain_ids(&a.end, bound, out);
            collect_free_plain_ids(&a.func, bound, out);
            collect_free_plain_ids(&a.op, bound, out);
            collect_free_plain_ids(&a.seed, bound, out);
        }
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(a)) => {
            collect_binary(&a.set, &a.func, bound, out)
        }
        Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(a)) => {
            collect_binary(&a.set, &a.func, bound, out)
        }
        Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(a)) => {
            collect_free_plain_ids(&a.set, bound, out);
            collect_free_plain_ids(&a.func, bound, out);
            collect_free_plain_ids(&a.op, bound, out);
            collect_free_plain_ids(&a.seed, bound, out);
        }
        Obj::SetFormer(SetFormer::Range(a)) => collect_binary(&a.start, &a.end, bound, out),
        Obj::SetFormer(SetFormer::ClosedRange(a)) => collect_binary(&a.start, &a.end, bound, out),
        Obj::SetFormer(SetFormer::FiniteSeqSet(a)) => {
            collect_free_plain_ids(&a.set, bound, out);
            collect_free_plain_ids(&a.n, bound, out);
        }
        Obj::SetFormer(SetFormer::SeqSet(a)) => collect_free_plain_ids(&a.set, bound, out),
        Obj::ProductShape(ProductShape::ObjAtIndex(a)) => {
            collect_free_plain_ids(&a.obj, bound, out);
            collect_free_plain_ids(&a.index, bound, out);
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(a)) => {
            for o in &a.params {
                collect_free_plain_ids(o, bound, out);
            }
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(a)) => {
            collect_free_plain_ids(&a.obj, bound, out);
        }
        Obj::InstantiatedTemplateObj(a) => {
            for o in &a.args {
                collect_free_plain_ids(o, bound, out);
            }
        }
        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(i)) => match i {
            crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::LeftOpen(s)
            | crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::LeftClosed(s)
            | crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::RightOpen(s)
            | crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::RightClosed(s) => {
                collect_free_plain_ids(&s.start, bound, out);
            }
        },
        Obj::SetFormer(SetFormer::IntervalObj(i)) => match i {
            crate::new_pipeline::ast::obj::IntervalObj::LeftOpenRightOpen(s)
            | crate::new_pipeline::ast::obj::IntervalObj::LeftOpenRightClosed(s)
            | crate::new_pipeline::ast::obj::IntervalObj::LeftClosedRightOpen(s)
            | crate::new_pipeline::ast::obj::IntervalObj::LeftClosedRightClosed(s) => {
                collect_free_plain_ids(&s.start, bound, out);
                collect_free_plain_ids(&s.end, bound, out);
            }
        },
        Obj::Literal(Literal::Number(_))
        | Obj::Literal(Literal::ImaginaryUnit(_))
        | Obj::Literal(Literal::EulerNumber(_))
        | Obj::Literal(Literal::Pi(_))
        | Obj::StandardSet(_) => {}
    }
}

fn collect_free_in_set_builder(
    sb: &SetBuilder,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    collect_free_plain_ids(&sb.param_set, bound, out);
    let mut bound2 = bound.clone();
    bound2.insert(sb.param_binding.id);
    for fact in &sb.facts {
        fact::collect_free_plain_ids_in_qf_fact(fact, &bound2, out);
    }
}

fn collect_free_in_anonymous_fn(
    af: &AnonymousFn,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    collect_free_in_fn_set(&af.body, bound, out);
    let binder_ids = binder_ids_from_set_bound_parameters(&af.body.set_bound_parameters);
    let mut bound2 = bound.clone();
    for id in binder_ids {
        bound2.insert(id);
    }
    collect_free_plain_ids(&af.equal_to, &bound2, out);
}

fn collect_free_in_fn_set(
    body: &FnSet,
    bound: &HashSet<IdentifierId>,
    out: &mut HashSet<IdentifierId>,
) {
    let mut bound2 = bound.clone();
    for group in &body.set_bound_parameters.groups {
        for param in &group.params {
            bound2.insert(param.id);
        }
        collect_free_plain_ids(&group.param_type, &bound2, out);
    }
    for fact in &body.dom_facts {
        fact::collect_free_plain_ids_in_qf_fact(fact, &bound2, out);
    }
    collect_free_plain_ids(&body.ret_set, &bound2, out);
}

pub fn shadow_binder_ids(
    param_to_arg_map: &HashMap<IdentifierId, Obj>,
    binder_ids: &[IdentifierId],
) -> HashMap<IdentifierId, Obj> {
    let mut shadowed = param_to_arg_map.clone();
    for id in binder_ids {
        shadowed.remove(id);
    }
    shadowed
}

pub fn binder_ids_from_set_bound_parameters(list: &SetBoundParameterList) -> Vec<IdentifierId> {
    let mut ids = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            ids.push(param.id);
        }
    }
    ids
}

pub fn binder_bound_names_from_set_bound_parameters(
    list: &SetBoundParameterList,
) -> Vec<BoundName> {
    let mut names = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            names.push(param.clone());
        }
    }
    names
}

impl Runtime {
    pub(crate) fn inst_set_builder(
        &mut self,
        sb: &SetBuilder,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<SetBuilder, InstError> {
        let param_set = self.inst_obj_rec(&sb.param_set, param_to_arg_map)?;
        let shadowed = shadow_binder_ids(param_to_arg_map, &[sb.param_binding.id]);
        let facts = self.inst_qf_facts_rec(&sb.facts, &shadowed)?;
        Ok(SetBuilder {
            param_binding: sb.param_binding.clone(),
            param_set: Box::new(param_set),
            facts,
        })
    }

    pub(crate) fn inst_fn_set(
        &mut self,
        fs: &FnSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<FnSet, InstError> {
        let binder_ids = binder_ids_from_set_bound_parameters(&fs.set_bound_parameters);
        let shadowed = shadow_binder_ids(param_to_arg_map, &binder_ids);
        let mut groups = Vec::with_capacity(fs.set_bound_parameters.groups.len());
        for group in &fs.set_bound_parameters.groups {
            let param_type = self.inst_obj_rec(&group.param_type, &shadowed)?;
            groups.push(SetBoundParameterGroup {
                params: group.params.clone(),
                param_type: Box::new(param_type),
            });
        }
        let dom_facts = self.inst_qf_facts_rec(&fs.dom_facts, &shadowed)?;
        let ret_set = self.inst_obj_rec(&fs.ret_set, &shadowed)?;
        Ok(FnSet {
            set_bound_parameters: SetBoundParameterList { groups },
            dom_facts,
            ret_set: Box::new(ret_set),
        })
    }

    pub(crate) fn inst_anonymous_fn(
        &mut self,
        af: &AnonymousFn,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<AnonymousFn, InstError> {
        let body = self.inst_fn_set(&af.body, param_to_arg_map)?;
        let binder_ids = binder_ids_from_set_bound_parameters(&af.body.set_bound_parameters);
        let shadowed = shadow_binder_ids(param_to_arg_map, &binder_ids);
        let equal_to = self.inst_obj_rec(&af.equal_to, &shadowed)?;
        Ok(AnonymousFn {
            body,
            equal_to: Box::new(equal_to),
        })
    }
}
