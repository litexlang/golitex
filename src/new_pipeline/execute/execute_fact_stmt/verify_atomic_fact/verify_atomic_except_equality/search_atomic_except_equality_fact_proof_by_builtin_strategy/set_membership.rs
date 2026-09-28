use super::result::*;
use crate::new_pipeline::ast::fact::{AtomicFact, InFact};
use crate::new_pipeline::ast::obj::{
    IntervalObj, Obj, ProductShape, SetFormer, SetOperator, StandardSet,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_cart_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
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
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            CartMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_union_membership_from_left_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<UnionMembershipFromLeftStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(
            inf.element.clone(),
            set.left.as_ref().clone(),
            inf.line_file.clone(),
        )];
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            UnionMembershipFromLeftStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_union_membership_from_right_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<UnionMembershipFromRightStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![self.strategy_in_fact(
            inf.element.clone(),
            set.right.as_ref().clone(),
            inf.line_file.clone(),
        )];
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            UnionMembershipFromRightStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_intersect_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<IntersectMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Intersect(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), set.left.as_ref().clone(), inf.line_file.clone()),
            self.strategy_in_fact(inf.element.clone(), set.right.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            IntersectMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_set_minus_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SetMinusMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::SetMinus(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), set.left.as_ref().clone(), inf.line_file.clone()),
            self.strategy_not_in_fact(inf.element.clone(), set.right.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            SetMinusMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_power_set_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PowerSetMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::PowerSet(set)) = &inf.set else { return Ok(None); };
        let requirements = vec![self.strategy_subset_fact(
            inf.element.clone(),
            set.set.as_ref().clone(),
            inf.line_file.clone(),
        )];
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            PowerSetMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_range_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<RangeMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::Range(range)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_less_equal_fact(range.start.as_ref().clone(), inf.element.clone(), inf.line_file.clone()),
            self.strategy_less_fact(inf.element.clone(), range.end.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            RangeMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_closed_range_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ClosedRangeMembershipStrategySingleStep>> {
        let Some(inf) = as_in(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::ClosedRange(range)) = &inf.set else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(inf.element.clone(), Obj::StandardSet(StandardSet::Z), inf.line_file.clone()),
            self.strategy_less_equal_fact(range.start.as_ref().clone(), inf.element.clone(), inf.line_file.clone()),
            self.strategy_less_equal_fact(inf.element.clone(), range.end.as_ref().clone(), inf.line_file.clone()),
        ];
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            ClosedRangeMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    pub(super) fn search_interval_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
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
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            IntervalMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
    }

    // Direct set-builder only (no definition transport / template unfold).
    pub(super) fn search_set_builder_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
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
                Ok(qf) => crate::new_pipeline::instantiate::quantifier_free_fact_to_fact(qf),
                Err(_) => return Ok(None),
            };
            requirements.push(instantiated);
        }
        finish(self, requirements, verify_state, |requirement_facts, proof_of_requirement_facts| {
            SetBuilderMembershipStrategySingleStep { requirement_facts, proof_of_requirement_facts }
        })
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

fn finish<T, F>(
    runtime: &mut Runtime,
    requirements: Vec<crate::new_pipeline::ast::fact::Fact>,
    verify_state: VerifyState,
    build: F,
) -> RuntimeResult<Option<T>>
where
    F: FnOnce(
        Vec<crate::new_pipeline::ast::fact::Fact>,
        Vec<crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult>,
    ) -> T,
{
    let Some((requirement_facts, proof_of_requirement_facts)) =
        runtime.verify_strategy_requirements(requirements, verify_state)?
    else {
        return Ok(None);
    };
    Ok(Some(build(requirement_facts, proof_of_requirement_facts)))
}
