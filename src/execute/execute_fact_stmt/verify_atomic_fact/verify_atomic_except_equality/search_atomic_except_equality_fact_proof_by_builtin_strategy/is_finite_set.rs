use super::result::*;
use crate::ast::fact::{AtomicFact, IsFiniteSetFact};
use crate::ast::obj::{FunctionSpace, Obj, ProductShape, SetFormer, SetOperator};
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_fn_range_finite_from_domain_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<FnRangeFiniteFromDomainStrategySingleStep>> {
        let Some(set) = as_finite_set(fact) else { return Ok(None); };
        let Obj::FunctionSpace(FunctionSpace::FnRange(fn_range)) = set else { return Ok(None); };
        // Only literal AnonymousFn bodies (no env lookup of named functions).
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = fn_range.function.as_ref() else {
            return Ok(None);
        };
        let mut param_count = 0;
        let mut domain = None;
        for group in &anon.body.set_bound_parameters.groups {
            param_count += group.params.len();
            if domain.is_none() {
                domain = Some(group.param_type.as_ref().clone());
            }
        }
        if param_count != 1 {
            return Ok(None);
        }
        let Some(domain) = domain else { return Ok(None); };
        let lf = match fact {
            AtomicFact::IsFiniteSetFact(f) => f.line_file.clone(),
            _ => None,
        };
        let requirements = vec![self.strategy_is_finite_set_fact(domain, lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(FnRangeFiniteFromDomainStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_power_set_finite_from_base_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<PowerSetFiniteFromBaseStrategySingleStep>> {
        let Some(set) = as_finite_set(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::PowerSet(power)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_finite_set_fact(power.set.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(PowerSetFiniteFromBaseStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_set_builder_finite_from_param_set_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<SetBuilderFiniteFromParamSetStrategySingleStep>> {
        let Some(set) = as_finite_set(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::SetBuilder(builder)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_finite_set_fact(builder.param_set.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(SetBuilderFiniteFromParamSetStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_union_finite_from_both_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<UnionFiniteFromBothStrategySingleStep>> {
        let Some(set) = as_finite_set(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(u)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![
            self.strategy_is_finite_set_fact(u.left.as_ref().clone(), lf.clone()),
            self.strategy_is_finite_set_fact(u.right.as_ref().clone(), lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(UnionFiniteFromBothStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_intersect_finite_from_both_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<IntersectFiniteFromBothStrategySingleStep>> {
        let Some(set) = as_finite_set(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Intersect(i)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![
            self.strategy_is_finite_set_fact(i.left.as_ref().clone(), lf.clone()),
            self.strategy_is_finite_set_fact(i.right.as_ref().clone(), lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntersectFiniteFromBothStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_set_minus_finite_from_left_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<SetMinusFiniteFromLeftStrategySingleStep>> {
        let Some(set) = as_finite_set(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::SetMinus(s)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_finite_set_fact(s.left.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(SetMinusFiniteFromLeftStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_cart_finite_from_factors_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<CartFiniteFromFactorsStrategySingleStep>> {
        let Some(set) = as_finite_set(fact) else { return Ok(None); };
        let Obj::ProductShape(ProductShape::Cart(cart)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let mut requirements = Vec::new();
        for factor in &cart.args {
            requirements.push(self.strategy_is_finite_set_fact(factor.as_ref().clone(), lf.clone()));
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(CartFiniteFromFactorsStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }
}

fn as_finite_set(fact: &AtomicFact) -> Option<&Obj> {
    match fact {
        AtomicFact::IsFiniteSetFact(IsFiniteSetFact { set, .. }) => Some(set),
        _ => None,
    }
}

fn line_file(fact: &AtomicFact) -> Option<crate::ast::line_file::SourceLine> {
    match fact {
        AtomicFact::IsFiniteSetFact(f) => f.line_file.clone(),
        _ => None,
    }
}
