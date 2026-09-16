use std::collections::{HashMap, HashSet};

use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    AnonymousFn, AnonymousFnBody, FnSet, FnSetBody, Obj, SetBuilder, SetBuilderBody,
};
use crate::new_pipeline::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::new_pipeline::runtime::Runtime;

use super::error::InstError;
use super::fact;

fn collect_unary(arg: &Obj, bound: &HashSet<String>, out: &mut HashSet<String>) {
    collect_free_plain_names(arg, bound, out);
}

fn collect_obj_list(list: &[Box<Obj>], bound: &HashSet<String>, out: &mut HashSet<String>) {
    for o in list {
        collect_free_plain_names(o, bound, out);
    }
}

fn collect_binary(left: &Obj, right: &Obj, bound: &HashSet<String>, out: &mut HashSet<String>) {
    collect_free_plain_names(left, bound, out);
    collect_free_plain_names(right, bound, out);
}

fn collect_ternary(
    a: &Obj,
    b: &Obj,
    c: &Obj,
    bound: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    collect_free_plain_names(a, bound, out);
    collect_free_plain_names(b, bound, out);
    collect_free_plain_names(c, bound, out);
}

pub fn fresh_binder_name(counter: &mut u64) -> String {
    let name = format!("□{}", counter);
    *counter += 1;
    name
}

pub fn free_plain_names_in_subst(subst: &HashMap<String, Obj>) -> HashSet<String> {
    let mut names = HashSet::new();
    for obj in subst.values() {
        collect_free_plain_names(obj, &HashSet::new(), &mut names);
    }
    names
}

pub fn collect_free_plain_names(
    obj: &Obj,
    bound: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    match obj {
        Obj::Identifier(id) => {
            if let AtomicName::Plain { name } = &id.name {
                if !bound.contains(name) {
                    out.insert(name.clone());
                }
            }
        }
        Obj::FnObj(f) => {
            match f.head.as_ref() {
                crate::new_pipeline::ast::obj::FnObjHead::Identifier(id) => {
                    collect_free_plain_names(&Obj::Identifier(id.clone()), bound, out);
                }
                crate::new_pipeline::ast::obj::FnObjHead::AnonymousFnLiteral(af) => {
                    collect_free_in_anonymous_fn_body(&af.surface, bound, out);
                    collect_free_in_anonymous_fn_body(&af.alpha, bound, out);
                }
                crate::new_pipeline::ast::obj::FnObjHead::FiniteSeqListObj(a) => {
                    for o in &a.objs {
                        collect_free_plain_names(o, bound, out);
                    }
                }
                crate::new_pipeline::ast::obj::FnObjHead::ObjAtIndex(a) => {
                    collect_free_plain_names(&a.obj, bound, out);
                    collect_free_plain_names(&a.index, bound, out);
                }
                crate::new_pipeline::ast::obj::FnObjHead::ObjAsStructInstanceWithFieldAccess(a) => {
                    collect_free_plain_names(&a.obj, bound, out);
                    if let Some(carrier) = &a.resolved_struct_carrier {
                        for o in &carrier.params {
                            collect_free_plain_names(o, bound, out);
                        }
                    }
                }
                crate::new_pipeline::ast::obj::FnObjHead::InstantiatedTemplateObj(a) => {
                    for o in &a.args {
                        collect_free_plain_names(o, bound, out);
                    }
                }
            }
            for group in &f.body {
                for o in group {
                    collect_free_plain_names(o, bound, out);
                }
            }
        }
        Obj::Add(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Sub(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Mul(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Div(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Mod(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Quot(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Gcd(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Lcm(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Min(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Max(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Pow(a) => {
            collect_free_plain_names(&a.base, bound, out);
            collect_free_plain_names(&a.exponent, bound, out);
        }
        Obj::Log(a) => {
            collect_free_plain_names(&a.base, bound, out);
            collect_free_plain_names(&a.arg, bound, out);
        }
        Obj::Floor(a) => collect_unary(&a.arg, bound, out),
        Obj::Ceil(a) => collect_unary(&a.arg, bound, out),
        Obj::Exp(a) => collect_unary(&a.arg, bound, out),
        Obj::Ln(a) => collect_unary(&a.arg, bound, out),
        Obj::Sign(a) => collect_unary(&a.arg, bound, out),
        Obj::Factorial(a) => collect_unary(&a.arg, bound, out),
        Obj::Abs(a) => collect_unary(&a.arg, bound, out),
        Obj::Sin(a) => collect_unary(&a.arg, bound, out),
        Obj::Arcsin(a) => collect_unary(&a.arg, bound, out),
        Obj::Cos(a) => collect_unary(&a.arg, bound, out),
        Obj::Tan(a) => collect_unary(&a.arg, bound, out),
        Obj::Cot(a) => collect_unary(&a.arg, bound, out),
        Obj::RealPart(a) => collect_unary(&a.arg, bound, out),
        Obj::ImaginaryPart(a) => collect_unary(&a.arg, bound, out),
        Obj::ComplexAbs(a) => collect_unary(&a.arg, bound, out),
        Obj::Sqrt(a) => collect_unary(&a.arg, bound, out),
        Obj::Union(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::Intersect(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::SetMinus(a) => collect_binary(&a.left, &a.right, bound, out),
        Obj::BigUnion(a) => collect_free_plain_names(&a.left, bound, out),
        Obj::BigIntersect(a) => collect_free_plain_names(&a.left, bound, out),
        Obj::IndexUnion(a) => {
            collect_free_plain_names(&a.index_set, bound, out);
            collect_free_plain_names(&a.ambient_set, bound, out);
            collect_free_plain_names(&a.family_fn, bound, out);
        }
        Obj::IndexIntersect(a) => {
            collect_free_plain_names(&a.index_set, bound, out);
            collect_free_plain_names(&a.ambient_set, bound, out);
            collect_free_plain_names(&a.family_fn, bound, out);
        }
        Obj::PowerSet(a) => collect_free_plain_names(&a.set, bound, out),
        Obj::GeneralCart(a) => {
            collect_free_plain_names(&a.index_set, bound, out);
            collect_free_plain_names(&a.family_set, bound, out);
            collect_free_plain_names(&a.family_fn, bound, out);
        }
        Obj::ListSet(a) => {
            for o in &a.list {
                collect_free_plain_names(o, bound, out);
            }
        }
        Obj::SetBuilder(sb) => {
            collect_free_plain_names(&sb.surface.param_set, bound, out);
            let mut bound2 = bound.clone();
            bound2.insert(sb.surface.param_binding.clone());
            for fact in &sb.surface.facts {
                fact::collect_free_plain_names_in_qf_fact(fact, &bound2, out);
            }
        }
        Obj::FnSet(fs) => collect_free_in_fn_set_body(&fs.surface, bound, out),
        Obj::AnonymousFn(af) => {
            collect_free_in_anonymous_fn_body(&af.surface, bound, out);
            collect_free_in_anonymous_fn_body(&af.alpha, bound, out);
        }
        Obj::Cart(a) => collect_obj_list(&a.args, bound, out),
        Obj::Tuple(a) => collect_obj_list(&a.args, bound, out),
        Obj::CartDim(a) => collect_free_plain_names(&a.set, bound, out),
        Obj::Proj(a) => {
            collect_free_plain_names(&a.set, bound, out);
            collect_free_plain_names(&a.dim, bound, out);
        }
        Obj::TupleDim(a) => collect_free_plain_names(&a.arg, bound, out),
        Obj::FiniteSetSize(a) => collect_free_plain_names(&a.set, bound, out),
        Obj::FiniteSetMax(a) => collect_free_plain_names(&a.set, bound, out),
        Obj::FiniteSetMin(a) => collect_free_plain_names(&a.set, bound, out),
        Obj::FnRange(a) => collect_free_plain_names(&a.function, bound, out),
        Obj::Replacement(a) => collect_free_plain_names(&a.source_set, bound, out),
        Obj::Sum(a) => collect_ternary(&a.start, &a.end, &a.func, bound, out),
        Obj::Product(a) => collect_ternary(&a.start, &a.end, &a.func, bound, out),
        Obj::Reduce(a) => {
            collect_free_plain_names(&a.start, bound, out);
            collect_free_plain_names(&a.end, bound, out);
            collect_free_plain_names(&a.func, bound, out);
            collect_free_plain_names(&a.op, bound, out);
            collect_free_plain_names(&a.seed, bound, out);
        }
        Obj::SumOfFiniteSet(a) => collect_binary(&a.set, &a.func, bound, out),
        Obj::ProductOfFiniteSet(a) => collect_binary(&a.set, &a.func, bound, out),
        Obj::FiniteSetReduce(a) => {
            collect_free_plain_names(&a.set, bound, out);
            collect_free_plain_names(&a.func, bound, out);
            collect_free_plain_names(&a.op, bound, out);
            collect_free_plain_names(&a.seed, bound, out);
        }
        Obj::Range(a) => collect_binary(&a.start, &a.end, bound, out),
        Obj::ClosedRange(a) => collect_binary(&a.start, &a.end, bound, out),
        Obj::FiniteSeqSet(a) => {
            collect_free_plain_names(&a.set, bound, out);
            collect_free_plain_names(&a.n, bound, out);
        }
        Obj::SeqSet(a) => collect_free_plain_names(&a.set, bound, out),
        Obj::FiniteSeqListObj(a) => {
            for o in &a.objs {
                collect_free_plain_names(o, bound, out);
            }
        }
        Obj::ObjAtIndex(a) => {
            collect_free_plain_names(&a.obj, bound, out);
            collect_free_plain_names(&a.index, bound, out);
        }
        Obj::StructObj(a) => {
            for o in &a.params {
                collect_free_plain_names(o, bound, out);
            }
        }
        Obj::ObjAsStructInstanceWithFieldAccess(a) => {
            collect_free_plain_names(&a.obj, bound, out);
            if let Some(carrier) = &a.resolved_struct_carrier {
                for o in &carrier.params {
                    collect_free_plain_names(o, bound, out);
                }
            }
        }
        Obj::InstantiatedTemplateObj(a) => {
            for o in &a.args {
                collect_free_plain_names(o, bound, out);
            }
        }
        Obj::OneSideInfinityIntervalObj(i) => match i {
            crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::LeftOpen(s)
            | crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::LeftClosed(s)
            | crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::RightOpen(s)
            | crate::new_pipeline::ast::obj::OneSideInfinityIntervalObj::RightClosed(s) => {
                collect_free_plain_names(&s.start, bound, out);
            }
        },
        Obj::IntervalObj(i) => match i {
            crate::new_pipeline::ast::obj::IntervalObj::LeftOpenRightOpen(s)
            | crate::new_pipeline::ast::obj::IntervalObj::LeftOpenRightClosed(s)
            | crate::new_pipeline::ast::obj::IntervalObj::LeftClosedRightOpen(s)
            | crate::new_pipeline::ast::obj::IntervalObj::LeftClosedRightClosed(s) => {
                collect_free_plain_names(&s.start, bound, out);
                collect_free_plain_names(&s.end, bound, out);
            }
        },
        Obj::Number(_)
        | Obj::ImaginaryUnit(_)
        | Obj::EulerNumber(_)
        | Obj::Pi(_)
        | Obj::StandardSet(_) => {}
    }
}

fn collect_free_in_anonymous_fn_body(body: &AnonymousFnBody, bound: &HashSet<String>, out: &mut HashSet<String>) {
    collect_free_in_fn_set_body(&body.body, bound, out);
    collect_free_plain_names(&body.equal_to, bound, out);
}

fn collect_free_in_fn_set_body(body: &FnSetBody, bound: &HashSet<String>, out: &mut HashSet<String>) {
    let mut bound2 = bound.clone();
    for group in &body.set_bound_parameters.groups {
        for param in &group.params {
            bound2.insert(param.clone());
        }
        collect_free_plain_names(&group.param_type, &bound2, out);
    }
    for fact in &body.dom_facts {
        fact::collect_free_plain_names_in_qf_fact(fact, &bound2, out);
    }
    collect_free_plain_names(&body.ret_set, &bound2, out);
}

pub fn prepare_binders(
    names: &[String],
    param_to_arg_map: &HashMap<String, Obj>,
    fresh_counter: &mut u64,
) -> Vec<(String, String)> {
    let free = free_plain_names_in_subst(param_to_arg_map);
    names
        .iter()
        .map(|name| {
            if free.contains(name) {
                (name.clone(), fresh_binder_name(fresh_counter))
            } else {
                (name.clone(), name.clone())
            }
        })
        .collect()
}

pub fn shadowed_subst_and_renames(
    param_to_arg_map: &HashMap<String, Obj>,
    binder_renames: &HashMap<String, String>,
    binders: &[(String, String)],
) -> (HashMap<String, Obj>, HashMap<String, String>) {
    let mut shadowed = param_to_arg_map.clone();
    for (name, _) in binders {
        shadowed.remove(name);
    }
    let mut new_renames = binder_renames.clone();
    for (old, new) in binders {
        new_renames.insert(old.clone(), new.clone());
    }
    (shadowed, new_renames)
}

pub fn binder_names_from_set_bound_parameters(list: &SetBoundParameterList) -> Vec<String> {
    let mut names = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            names.push(param.clone());
        }
    }
    names
}

impl Runtime {
    fn inst_set_builder_body_contents(
        &mut self,
        body: &SetBuilderBody,
        binders: &[(String, String)],
        param_set: Obj,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<SetBuilderBody, InstError> {
        let facts = self.inst_qf_facts_rec(&body.facts, param_to_arg_map, fresh, binder_renames)?;
        Ok(SetBuilderBody {
            param_binding: binders[0].1.clone(),
            param_set: Box::new(param_set),
            facts,
        })
    }

    fn inst_set_builder_body(
        &mut self,
        body: &SetBuilderBody,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<SetBuilderBody, InstError> {
        let param_set = self.inst_obj_rec(&body.param_set, param_to_arg_map, fresh, binder_renames)?;
        let binders = prepare_binders(&[body.param_binding.clone()], param_to_arg_map, fresh);
        let (shadowed, new_renames) =
            shadowed_subst_and_renames(param_to_arg_map, binder_renames, &binders);
        self.inst_set_builder_body_contents(
            body,
            &binders,
            param_set,
            &shadowed,
            fresh,
            &new_renames,
        )
    }

    fn inst_fn_set_body_contents(
        &mut self,
        body: &FnSetBody,
        binders: &[(String, String)],
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<FnSetBody, InstError> {
        let mut rename_iter = binders.iter();
        let mut groups = Vec::with_capacity(body.set_bound_parameters.groups.len());
        for group in &body.set_bound_parameters.groups {
            let param_type =
                self.inst_obj_rec(&group.param_type, param_to_arg_map, fresh, binder_renames)?;
            let mut params = Vec::with_capacity(group.params.len());
            for _ in &group.params {
                let (_, new_name) = rename_iter.next().expect("binder count matches");
                params.push(new_name.clone());
            }
            groups.push(SetBoundParameterGroup {
                params,
                param_type: Box::new(param_type),
            });
        }
        let dom_facts = self.inst_qf_facts_rec(&body.dom_facts, param_to_arg_map, fresh, binder_renames)?;
        let ret_set = self.inst_obj_rec(&body.ret_set, param_to_arg_map, fresh, binder_renames)?;
        Ok(FnSetBody {
            set_bound_parameters: SetBoundParameterList { groups },
            dom_facts,
            ret_set: Box::new(ret_set),
        })
    }

    fn inst_fn_set_body(
        &mut self,
        body: &FnSetBody,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<FnSetBody, InstError> {
        let binder_names = binder_names_from_set_bound_parameters(&body.set_bound_parameters);
        let binders = prepare_binders(&binder_names, param_to_arg_map, fresh);
        let (shadowed, new_renames) =
            shadowed_subst_and_renames(param_to_arg_map, binder_renames, &binders);
        self.inst_fn_set_body_contents(body, &binders, &shadowed, fresh, &new_renames)
    }

    pub(crate) fn inst_set_builder(
        &mut self,
        sb: &SetBuilder,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<SetBuilder, InstError> {
        let surface = self.inst_set_builder_body(&sb.surface, param_to_arg_map, fresh, binder_renames)?;
        let alpha = self.inst_set_builder_body(&sb.alpha, param_to_arg_map, fresh, binder_renames)?;
        Ok(SetBuilder { surface, alpha })
    }

    pub(crate) fn inst_fn_set(
        &mut self,
        fs: &FnSet,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<FnSet, InstError> {
        let surface = self.inst_fn_set_body(&fs.surface, param_to_arg_map, fresh, binder_renames)?;
        let alpha = self.inst_fn_set_body(&fs.alpha, param_to_arg_map, fresh, binder_renames)?;
        Ok(FnSet { surface, alpha })
    }

    fn inst_anonymous_fn_body_inner(
        &mut self,
        body: &AnonymousFnBody,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<AnonymousFnBody, InstError> {
        let binder_names = binder_names_from_set_bound_parameters(&body.body.set_bound_parameters);
        let binders = prepare_binders(&binder_names, param_to_arg_map, fresh);
        let (shadowed, new_renames) =
            shadowed_subst_and_renames(param_to_arg_map, binder_renames, &binders);
        let fn_body =
            self.inst_fn_set_body_contents(&body.body, &binders, &shadowed, fresh, &new_renames)?;
        let equal_to = self.inst_obj_rec(&body.equal_to, &shadowed, fresh, &new_renames)?;
        Ok(AnonymousFnBody {
            body: fn_body,
            equal_to: Box::new(equal_to),
        })
    }

    pub(crate) fn inst_anonymous_fn(
        &mut self,
        af: &AnonymousFn,
        param_to_arg_map: &HashMap<String, Obj>,
        fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<AnonymousFn, InstError> {
        Ok(AnonymousFn {
            surface: self.inst_anonymous_fn_body_inner(
                &af.surface,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?,
            alpha: self.inst_anonymous_fn_body_inner(
                &af.alpha,
                param_to_arg_map,
                fresh,
                binder_renames,
            )?,
        })
    }
}
