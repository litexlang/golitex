use super::result::*;
use crate::ast::fact::{AtomicFact, IsNonemptySetFact};
use crate::ast::obj::{FunctionSpace, IntervalObj, Obj, ProductShape, SetFormer, SetOperator};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_closed_range_nonempty_from_endpoint_order_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ClosedRangeNonemptyFromEndpointOrderStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::ClosedRange(r)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_less_equal_fact(
            r.start.as_ref().clone(),
            r.end.as_ref().clone(),
            lf,
        )];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(ClosedRangeNonemptyFromEndpointOrderStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_range_nonempty_from_endpoint_order_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<RangeNonemptyFromEndpointOrderStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::Range(r)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_less_fact(
            r.start.as_ref().clone(),
            r.end.as_ref().clone(),
            lf,
        )];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(RangeNonemptyFromEndpointOrderStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_interval_nonempty_from_endpoint_order_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<IntervalNonemptyFromEndpointOrderStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::IntervalObj(interval)) = set else { return Ok(None); };
        let (start, end, left_closed, right_closed) = interval_bounds(interval);
        let lf = line_file(fact);
        let requirements = if left_closed && right_closed {
            vec![self.strategy_less_equal_fact(start, end, lf)]
        } else {
            vec![self.strategy_less_fact(start, end, lf)]
        };
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(IntervalNonemptyFromEndpointOrderStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_union_nonempty_from_left_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<UnionNonemptyFromLeftStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(u)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_nonempty_set_fact(u.left.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(UnionNonemptyFromLeftStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_union_nonempty_from_right_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<UnionNonemptyFromRightStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(u)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_nonempty_set_fact(u.right.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(UnionNonemptyFromRightStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_cart_nonempty_from_all_factors_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CartNonemptyFromAllFactorsStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::ProductShape(ProductShape::Cart(cart)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let mut requirements = Vec::new();
        for factor in &cart.args {
            requirements.push(self.strategy_is_nonempty_set_fact(factor.as_ref().clone(), lf.clone()));
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(CartNonemptyFromAllFactorsStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_fn_set_nonempty_from_codomain_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FnSetNonemptyFromCodomainStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_nonempty_set_fact(fn_set.ret_set.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(FnSetNonemptyFromCodomainStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_anonymous_fn_nonempty_from_codomain_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AnonymousFnNonemptyFromCodomainStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_nonempty_set_fact(anon.body.ret_set.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(AnonymousFnNonemptyFromCodomainStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_finite_seq_set_nonempty_from_codomain_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FiniteSeqSetNonemptyFromCodomainStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::FiniteSeqSet(seq)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_nonempty_set_fact(seq.set.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(FiniteSeqSetNonemptyFromCodomainStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_seq_set_nonempty_from_codomain_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SeqSetNonemptyFromCodomainStrategySingleStep>> {
        let Some(set) = as_nonempty_set(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::SeqSet(seq)) = set else { return Ok(None); };
        let lf = line_file(fact);
        let requirements = vec![self.strategy_is_nonempty_set_fact(seq.set.as_ref().clone(), lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else { return Ok(None); };
        Ok(Some(SeqSetNonemptyFromCodomainStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}

fn as_nonempty_set(fact: &AtomicFact) -> Option<&Obj> {
    match fact {
        AtomicFact::IsNonemptySetFact(IsNonemptySetFact { set, .. }) => Some(set),
        _ => None,
    }
}

fn line_file(fact: &AtomicFact) -> Option<crate::ast::line_file::SourceLine> {
    match fact {
        AtomicFact::IsNonemptySetFact(f) => f.line_file.clone(),
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
