use super::helper::{is_zero_obj, zero_obj};
use super::result::{
    NonnegativeSumIsNonnegativeStrategySingleStep, PosAddPosIsPosStrategySingleStep,
    StrictAdditiveLeftStrictStrategySingleStep, StrictAdditiveRightStrictStrategySingleStep,
};
use crate::ast::fact::{AtomicFact, GreaterEqualFact, GreaterFact, LessEqualFact, LessFact};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{ArithmeticOperator, Obj};
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_pos_add_pos_is_pos_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<PosAddPosIsPosStrategySingleStep>> {
        let Some((l, r, lf)) = positive_sum_goal_summands(fact) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_greater_fact(l, zero_obj(), lf.clone()),
            self.strategy_greater_fact(r, zero_obj(), lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(PosAddPosIsPosStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_nonnegative_sum_is_nonnegative_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<NonnegativeSumIsNonnegativeStrategySingleStep>> {
        let Some((l, r, lf)) = nonnegative_sum_goal_summands(fact) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(zero_obj(), l, lf.clone()),
            self.strategy_less_equal_fact(zero_obj(), r, lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(NonnegativeSumIsNonnegativeStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_strict_additive_left_strict_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<StrictAdditiveLeftStrictStrategySingleStep>> {
        let Some((l, r, lf)) = positive_sum_goal_summands(fact) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_fact(zero_obj(), l, lf.clone()),
            self.strategy_less_equal_fact(zero_obj(), r, lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(StrictAdditiveLeftStrictStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_strict_additive_right_strict_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<StrictAdditiveRightStrictStrategySingleStep>> {
        let Some((l, r, lf)) = positive_sum_goal_summands(fact) else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_less_equal_fact(zero_obj(), l, lf.clone()),
            self.strategy_less_fact(zero_obj(), r, lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(StrictAdditiveRightStrictStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}

fn add_summands(obj: &Obj) -> Option<(Obj, Obj)> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) = obj {
        Some((add.left.as_ref().clone(), add.right.as_ref().clone()))
    } else {
        None
    }
}

fn positive_sum_goal_summands(fact: &AtomicFact) -> Option<(Obj, Obj, Option<SourceLine>)> {
    match fact {
        AtomicFact::GreaterFact(GreaterFact { left, right, line_file, .. }) if is_zero_obj(right) => {
            let (l, r) = add_summands(left)?;
            Some((l, r, line_file.clone()))
        }
        AtomicFact::LessFact(LessFact { left, right, line_file, .. }) if is_zero_obj(left) => {
            let (l, r) = add_summands(right)?;
            Some((l, r, line_file.clone()))
        }
        _ => None,
    }
}

fn nonnegative_sum_goal_summands(fact: &AtomicFact) -> Option<(Obj, Obj, Option<SourceLine>)> {
    match fact {
        AtomicFact::GreaterEqualFact(GreaterEqualFact { left, right, line_file, .. })
            if is_zero_obj(right) =>
        {
            let (l, r) = add_summands(left)?;
            Some((l, r, line_file.clone()))
        }
        AtomicFact::LessEqualFact(LessEqualFact { left, right, line_file, .. })
            if is_zero_obj(left) =>
        {
            let (l, r) = add_summands(right)?;
            Some((l, r, line_file.clone()))
        }
        _ => None,
    }
}
