use super::result::*;
use crate::ast::fact::{AtomicFact, Fact, InFact};
use crate::ast::obj::{
    FnObj, FnObjHead, FunctionSpace, IntervalObj, Obj, ProductShape, SetFormer, SetOperator,
    StandardSet, StructAndFieldAccessObj,
};
use crate::ast::param::SetBoundParameterList;
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::standard_set_is_subset_eq;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    pub(super) fn search_cart_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<CartMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::ProductShape(ProductShape::Cart(cart)) = &inf.set else { return Ok(None); };
        let Obj::ProductShape(ProductShape::Tuple(tuple)) = &inf.element else { return Ok(None); };
        if tuple.args.len() < 2 || tuple.args.len() != cart.args.len() {
            return Ok(None);
        }
        let mut requirements = Vec::new();
        for (element, set) in tuple.args.iter().zip(cart.args.iter()) {
            requirements.push(self.strategy_in_fact(
                element.as_ref().clone(),
                set.as_ref().clone(),
                inf.line_file.clone(),
            ));
        }
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            CartMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_union_membership_from_left_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<UnionMembershipFromLeftStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(
            inf.element.clone(),
            set.left.as_ref().clone(),
            inf.line_file.clone(),
        )];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            UnionMembershipFromLeftStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_union_membership_from_right_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<UnionMembershipFromRightStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(
            inf.element.clone(),
            set.right.as_ref().clone(),
            inf.line_file.clone(),
        )];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            UnionMembershipFromRightStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_intersect_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntersectMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Intersect(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), set.left.as_ref().clone(), inf.line_file.clone()),
            self.strategy_in_fact(inf.element.clone(), set.right.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            IntersectMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_set_minus_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<SetMinusMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::SetMinus(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), set.left.as_ref().clone(), inf.line_file.clone()),
            self.strategy_not_in_fact(inf.element.clone(), set.right.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            SetMinusMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_power_set_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<PowerSetMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::PowerSet(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![self.strategy_subset_fact(
            inf.element.clone(),
            set.set.as_ref().clone(),
            inf.line_file.clone(),
        )];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            PowerSetMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_range_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RangeMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::Range(range)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_less_equal_fact(range.start.as_ref().clone(), inf.element.clone(), inf.line_file.clone()),
            self.strategy_less_fact(inf.element.clone(), range.end.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            RangeMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_closed_range_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<ClosedRangeMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::ClosedRange(range)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_less_equal_fact(range.start.as_ref().clone(), inf.element.clone(), inf.line_file.clone()),
            self.strategy_less_equal_fact(inf.element.clone(), range.end.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            ClosedRangeMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_interval_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntervalMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::IntervalObj(interval)) = &inf.set else { return Ok(None); };
        let (start, end, left_closed, right_closed) = interval_bounds(interval);
        let left_bound = if left_closed {
            self.strategy_less_equal_fact(start, inf.element.clone(), inf.line_file.clone())
        } else {
            self.strategy_less_fact(start, inf.element.clone(), inf.line_file.clone())
        };
        let right_bound = if right_closed {
            self.strategy_less_equal_fact(inf.element.clone(), end, inf.line_file.clone())
        } else {
            self.strategy_less_fact(inf.element.clone(), end, inf.line_file.clone())
        };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), Obj::StandardSet(StandardSet::R), inf.line_file.clone()),
            left_bound,
            right_bound,
        ];
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            IntervalMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    // Direct set-builder only (no definition transport / template unfold).
    pub(super) fn search_set_builder_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<SetBuilderMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = &inf.set else { return Ok(None); };
        let mut requirements = Vec::new();
        requirements.push(self.strategy_in_fact(
            inf.element.clone(),
            builder.param_set.as_ref().clone(),
            inf.line_file.clone(),
        ));
        let mut subst = std::collections::HashMap::new();
        subst.insert(builder.param_binding.id, inf.element.clone());
        for defining in &builder.facts {
            let instantiated = match self.inst_quantifier_free_fact(defining, &subst) {
                Ok(qf) => crate::instantiate::quantifier_free_fact_to_fact(qf),
                Err(_) => return Ok(None),
            };
            requirements.push(instantiated);
        }
        finish(self, requirements, ctx, |requirement_facts, proof_of_requirement_facts| {
            SetBuilderMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    // Prove `x $in T` from `x $in S` (S ⊂ T among standard sets) as one strategy
    // step: known / nested strategy only for the source membership (e.g. `$in R`),
    // then ⊂-lift. Example: `dot(vec(a,b), vec(a,c)) $in C` via `$in R`.
    pub(super) fn search_standard_set_subset_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<StandardSetSubsetMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::StandardSet(target) = &inf.set else { return Ok(None); };
        let mut alternatives = Vec::new();
        for source in proper_subsets_in_membership_proof_order(target) {
            alternatives.push(vec![self.strategy_in_fact(
                inf.element.clone(),
                Obj::StandardSet(source),
                inf.line_file.clone(),
            )]);
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.try_strategy_requirement_alternatives(alternatives, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(StandardSetSubsetMembershipStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    // Prove `f(args) $in Ret` from domain memberships under strategy depth.
    // Example: `dot(vec(q,p), vec(q,r)) $in R` with nested `vec(...) $in cart(R,R)`.
    pub(super) fn search_fn_application_in_codomain_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<FnApplicationInCodomainStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::FnObj(fn_obj) = &inf.element else { return Ok(None); };
        // Field applications use the same signature evidence and domain
        // obligations as named functions, including equality-class candidates.
        let head_obj = match fn_obj.head.as_ref() {
            FnObjHead::Identifier(head) => Obj::Identifier(head.clone()),
            FnObjHead::FieldAccess(access) => {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()))
            }
            _ => return Ok(None),
        };
        let candidates = self.collect_in_function_set_candidates(&head_obj);
        for (fn_set, cite_signature_fact_id) in candidates {
            let Some(applied_ret) = self.applied_fn_set_return_set(fn_obj, &fn_set) else {
                continue;
            };
            if applied_ret.ir() != inf.set.ir() {
                continue;
            }
            let Some(requirements) =
                self.fn_app_domain_strategy_requirements(fn_obj, &fn_set, inf.line_file.clone())
            else {
                continue;
            };
            if let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, ctx)?
            {
                return Ok(Some(FnApplicationInCodomainStrategySingleStep {
                    cite_signature_fact_id,
                    requirement_facts,
                    proof_of_requirement_facts,
                }));
            }
        }
        Ok(None)
    }

    fn fn_app_domain_strategy_requirements(
        &mut self,
        value: &FnObj,
        fn_set: &crate::ast::obj::FnSet,
        line_file: Option<crate::ast::line_file::SourceLine>,
    ) -> Option<Vec<Fact>> {
        let mut requirements = Vec::new();
        let mut space = fn_set.clone();
        let last = value.body.len().checked_sub(1)?;
        for (layer_index, layer) in value.body.iter().enumerate() {
            let args: Vec<Obj> = layer.iter().map(|a| a.as_ref().clone()).collect();
            let expected = set_bound_parameter_count(&space.set_bound_parameters);
            if args.len() != expected {
                return None;
            }
            let mut arg_index = 0;
            for group in &space.set_bound_parameters.groups {
                let param_type = group.param_type.as_ref();
                for _param in &group.params {
                    requirements.push(self.strategy_in_fact(
                        args[arg_index].clone(),
                        param_type.clone(),
                        line_file.clone(),
                    ));
                    arg_index += 1;
                }
            }
            let subst = set_bound_params_to_arg_map(&space.set_bound_parameters, &args);
            for dom in &space.dom_facts {
                let instantiated = self.inst_quantifier_free_fact(dom, &subst).ok()?;
                requirements.push(quantifier_free_fact_to_fact(instantiated));
            }
            if layer_index < last {
                let next_ret = self.inst_obj(space.ret_set.as_ref(), &subst).ok()?;
                space = match next_ret {
                    Obj::FunctionSpace(FunctionSpace::FnSet(next)) => next,
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => anon.body,
                    _ => return None,
                };
            }
        }
        Some(requirements)
    }
}

fn as_in(fact: &AtomicFact) -> Option<&InFact> {
    match fact {
        AtomicFact::InFact(f) => Some(f),
        _ => None,
    }
}

fn interval_bounds(interval: &IntervalObj) -> (Obj, Obj, bool, bool) {
    match interval {
        IntervalObj::LeftOpenRightOpen(s) => (s.start.as_ref().clone(), s.end.as_ref().clone(), false, false),
        IntervalObj::LeftOpenRightClosed(s) => (s.start.as_ref().clone(), s.end.as_ref().clone(), false, true),
        IntervalObj::LeftClosedRightOpen(s) => (s.start.as_ref().clone(), s.end.as_ref().clone(), true, false),
        IntervalObj::LeftClosedRightClosed(s) => (s.start.as_ref().clone(), s.end.as_ref().clone(), true, true),
    }
}

fn proper_subsets_in_membership_proof_order(target: &StandardSet) -> Vec<StandardSet> {
    [
        StandardSet::R,
        StandardSet::Q,
        StandardSet::Z,
        StandardSet::N,
        StandardSet::RStar,
        StandardSet::RPos,
        StandardSet::RNeg,
        StandardSet::QStar,
        StandardSet::QPos,
        StandardSet::QNeg,
        StandardSet::ZStar,
        StandardSet::ZNeg,
        StandardSet::NPos,
        StandardSet::CStar,
    ]
    .into_iter()
    .filter(|source| source != target && standard_set_is_subset_eq(source, target))
    .collect()
}

fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

fn set_bound_params_to_arg_map(
    list: &SetBoundParameterList,
    args: &[Obj],
) -> HashMap<IdentifierId, Obj> {
    let mut map = HashMap::new();
    let mut i = 0;
    for group in &list.groups {
        for param in &group.params {
            if i < args.len() {
                map.insert(param.id, args[i].clone());
            }
            i += 1;
        }
    }
    map
}

fn finish<T, F>(
    runtime: &mut Runtime,
    requirements: Vec<Fact>,
    ctx: StrategySearch,
    build: F,
) -> RuntimeResult<Option<T>>
where
    F: FnOnce(
        Vec<Fact>,
        Vec<crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult>,
    ) -> T,
{
    let Some((requirement_facts, proof_of_requirement_facts)) =
        runtime.verify_strategy_requirements(requirements, ctx)?
    else {
        return Ok(None);
    };
    Ok(Some(build(requirement_facts, proof_of_requirement_facts)))
}
