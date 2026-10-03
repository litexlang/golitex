use super::result::*;
use crate::ast::fact::{AtomicFact, SubsetFact, SupersetFact};
use crate::ast::obj::{Obj, SetFormer, SetOperator};
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_list_set_subset_from_members_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<ListSetSubsetFromMembersStrategySingleStep>> {
        let Some((left, right, lf)) = as_subset_sides(fact) else { return Ok(None); };
        let Obj::SetFormer(SetFormer::ListSet(set)) = left else { return Ok(None); };
        let mut requirements = Vec::new();
        for element in &set.list {
            requirements.push(self.strategy_in_fact(element.as_ref().clone(), right.clone(), lf.clone()));
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(ListSetSubsetFromMembersStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_union_subset_from_both_operands_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<UnionSubsetFromBothOperandsStrategySingleStep>> {
        let Some((left, right, lf)) = as_subset_sides(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Union(set)) = left else { return Ok(None); };
        let requirements = vec![
            self.strategy_subset_fact(set.left.as_ref().clone(), right.clone(), lf.clone()),
            self.strategy_subset_fact(set.right.as_ref().clone(), right, lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(UnionSubsetFromBothOperandsStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_intersect_subset_from_left_operand_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<IntersectSubsetFromLeftOperandStrategySingleStep>> {
        let Some((left, right, lf)) = as_subset_sides(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Intersect(set)) = left else { return Ok(None); };
        let requirements = vec![self.strategy_subset_fact(set.left.as_ref().clone(), right, lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntersectSubsetFromLeftOperandStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_intersect_subset_from_right_operand_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<IntersectSubsetFromRightOperandStrategySingleStep>> {
        let Some((left, right, lf)) = as_subset_sides(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Intersect(set)) = left else { return Ok(None); };
        let requirements = vec![self.strategy_subset_fact(set.right.as_ref().clone(), right, lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(IntersectSubsetFromRightOperandStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_set_minus_subset_from_left_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<SetMinusSubsetFromLeftStrategySingleStep>> {
        let Some((left, right, lf)) = as_subset_sides(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::SetMinus(set)) = left else { return Ok(None); };
        let requirements = vec![self.strategy_subset_fact(set.left.as_ref().clone(), right, lf)];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(SetMinusSubsetFromLeftStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }

    pub(super) fn search_subset_of_intersect_from_both_bounds_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<SubsetOfIntersectFromBothBoundsStrategySingleStep>> {
        let Some((left, right, lf)) = as_subset_sides(fact) else { return Ok(None); };
        let Obj::SetOperator(SetOperator::Intersect(set)) = right else { return Ok(None); };
        let requirements = vec![
            self.strategy_subset_fact(left.clone(), set.left.as_ref().clone(), lf.clone()),
            self.strategy_subset_fact(left, set.right.as_ref().clone(), lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else { return Ok(None); };
        Ok(Some(SubsetOfIntersectFromBothBoundsStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }
}

// Accept SubsetFact, or SupersetFact flipped to subset order.
fn as_subset_sides(fact: &AtomicFact) -> Option<(Obj, Obj, Option<crate::ast::line_file::SourceLine>)> {
    match fact {
        AtomicFact::SubsetFact(SubsetFact { left, right, line_file, .. }) => {
            Some((left.clone(), right.clone(), line_file.clone()))
        }
        AtomicFact::SupersetFact(SupersetFact { left, right, line_file, .. }) => {
            // A $superset B means B $subset A
            Some((right.clone(), left.clone(), line_file.clone()))
        }
        _ => None,
    }
}
