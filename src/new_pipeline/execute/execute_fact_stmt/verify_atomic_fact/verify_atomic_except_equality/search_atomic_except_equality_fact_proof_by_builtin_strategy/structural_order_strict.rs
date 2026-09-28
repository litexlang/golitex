use super::helper::{is_zero_obj, two_obj, zero_obj};
use super::result::*;
use crate::new_pipeline::ast::fact::{AtomicFact, LessFact};
use crate::new_pipeline::ast::line_file::SourceLine;
use crate::new_pipeline::ast::obj::{Abs, ArithmeticOperator, Obj, Pow, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {

    pub(super) fn search_product_positive_both_pos_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProductPositiveBothPosStrategySingleStep>> {
        let Some((l, r, lf)) = zero_lt_mul(fact) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_fact(zero_obj(), l, lf.clone()),
            self.strategy_less_fact(zero_obj(), r, lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ProductPositiveBothPosStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_product_positive_both_neg_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProductPositiveBothNegStrategySingleStep>> {
        let Some((l, r, lf)) = zero_lt_mul(fact) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_fact(l, zero_obj(), lf.clone()),
            self.strategy_less_fact(r, zero_obj(), lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ProductPositiveBothNegStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_quotient_positive_same_sign_pos_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<QuotientPositiveSameSignPosStrategySingleStep>> {
        let Some((l, r, lf)) = zero_lt_div(fact) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_fact(zero_obj(), l, lf.clone()),
            self.strategy_less_fact(zero_obj(), r, lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(QuotientPositiveSameSignPosStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_quotient_positive_same_sign_neg_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<QuotientPositiveSameSignNegStrategySingleStep>> {
        let Some((l, r, lf)) = zero_lt_div(fact) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_fact(l, zero_obj(), lf.clone()),
            self.strategy_less_fact(r, zero_obj(), lf),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(QuotientPositiveSameSignNegStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_componentwise_strict_left_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AddComponentwiseStrictLeftStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(left), Some(right)) = (as_add(&lt.left), as_add(&lt.right)) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_fact(left.0, right.0, lt.line_file.clone()),
            self.strategy_less_equal_fact(left.1, right.1, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(AddComponentwiseStrictLeftStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_componentwise_strict_right_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AddComponentwiseStrictRightStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(left), Some(right)) = (as_add(&lt.left), as_add(&lt.right)) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_equal_fact(left.0, right.0, lt.line_file.clone()),
            self.strategy_less_fact(left.1, right.1, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(AddComponentwiseStrictRightStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_shared_subtrahend_less_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubSharedSubtrahendLessStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(left), Some(right)) = (as_sub(&lt.left), as_sub(&lt.right)) else { return Ok(None); };
        if left.1 != right.1 { return Ok(None); }
        let requirements = vec![self.strategy_less_fact(left.0, right.0, lt.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(SubSharedSubtrahendLessStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_shared_minuend_less_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubSharedMinuendLessStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(left), Some(right)) = (as_sub(&lt.left), as_sub(&lt.right)) else { return Ok(None); };
        if left.0 != right.0 { return Ok(None); }
        let requirements = vec![self.strategy_less_fact(right.1, left.1, lt.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(SubSharedMinuendLessStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_div_shared_positive_denom_less_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<DivSharedPositiveDenomLessStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(left), Some(right)) = (as_div(&lt.left), as_div(&lt.right)) else { return Ok(None); };
        if left.1 != right.1 { return Ok(None); }
        let requirements = vec![
            self.strategy_less_fact(zero_obj(), left.1.clone(), lt.line_file.clone()),
            self.strategy_less_fact(left.0, right.0, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(DivSharedPositiveDenomLessStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_div_shared_negative_denom_less_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<DivSharedNegativeDenomLessStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(left), Some(right)) = (as_div(&lt.left), as_div(&lt.right)) else { return Ok(None); };
        if left.1 != right.1 { return Ok(None); }
        let requirements = vec![
            self.strategy_less_fact(left.1.clone(), zero_obj(), lt.line_file.clone()),
            self.strategy_less_fact(right.0, left.0, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(DivSharedNegativeDenomLessStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_pow_shared_exponent_less_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PowSharedExponentLessStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(left), Some(right)) = (as_pow(&lt.left), as_pow(&lt.right)) else { return Ok(None); };
        if left.1 != right.1 { return Ok(None); }
        let requirements = vec![
            self.strategy_in_fact(left.1.clone(), Obj::StandardSet(StandardSet::NPos), lt.line_file.clone()),
            self.strategy_less_equal_fact(zero_obj(), left.0.clone(), lt.line_file.clone()),
            self.strategy_less_fact(left.0, right.0, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(PowSharedExponentLessStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_abs_vs_square_less_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AbsVsSquareLessStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(la), Some(ra)) = (as_abs(&lt.left), as_abs(&lt.right)) else { return Ok(None); };
        let requirements = vec![
            self.strategy_in_fact(la.clone(), Obj::StandardSet(StandardSet::R), lt.line_file.clone()),
            self.strategy_in_fact(ra.clone(), Obj::StandardSet(StandardSet::R), lt.line_file.clone()),
            self.strategy_less_fact(pow_obj(la, two_obj()), pow_obj(ra, two_obj()), lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(AbsVsSquareLessStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_right_strict_shift_left_strict_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AddRightStrictShiftLeftStrictStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let Some(add) = as_add(&lt.right) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_fact(lt.left.clone(), add.0, lt.line_file.clone()),
            self.strategy_less_equal_fact(zero_obj(), add.1, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(AddRightStrictShiftLeftStrictStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_right_strict_shift_left_weak_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AddRightStrictShiftLeftWeakStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let Some(add) = as_add(&lt.right) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_equal_fact(lt.left.clone(), add.0, lt.line_file.clone()),
            self.strategy_less_fact(zero_obj(), add.1, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(AddRightStrictShiftLeftWeakStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_right_strict_shift_right_strict_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AddRightStrictShiftRightStrictStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let Some(add) = as_add(&lt.right) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_fact(lt.left.clone(), add.1, lt.line_file.clone()),
            self.strategy_less_equal_fact(zero_obj(), add.0, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(AddRightStrictShiftRightStrictStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_add_right_strict_shift_right_weak_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AddRightStrictShiftRightWeakStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let Some(add) = as_add(&lt.right) else { return Ok(None); };
        let requirements = vec![
            self.strategy_less_equal_fact(lt.left.clone(), add.1, lt.line_file.clone()),
            self.strategy_less_fact(zero_obj(), add.0, lt.line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(AddRightStrictShiftRightWeakStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_positive_to_zero_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubPositiveToZeroStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        if !is_zero_obj(&lt.right) { return Ok(None); }
        let Some(sub) = as_sub(&lt.left) else { return Ok(None); };
        let requirements = vec![self.strategy_less_fact(sub.0, sub.1, lt.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(SubPositiveToZeroStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_sub_positive_from_zero_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubPositiveFromZeroStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        if !is_zero_obj(&lt.left) { return Ok(None); }
        let Some(sub) = as_sub(&lt.right) else { return Ok(None); };
        let requirements = vec![self.strategy_less_fact(sub.1, sub.0, lt.line_file.clone())];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(SubPositiveFromZeroStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    pub(super) fn search_common_positive_factor_less_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CommonPositiveFactorLessStrategySingleStep>> {
        let Some(lt) = as_lt(fact) else { return Ok(None); };
        let (Some(lm), Some(rm)) = (as_mul(&lt.left), as_mul(&lt.right)) else { return Ok(None); };
        let left_factors = [lm.0, lm.1];
        let right_factors = [rm.0, rm.1];
        let mut alts = Vec::new();
        for (li, lf) in left_factors.iter().enumerate() {
            for (ri, rf) in right_factors.iter().enumerate() {
                if lf != rf { continue; }
                alts.push(vec![
                    self.strategy_less_fact(zero_obj(), lf.clone(), lt.line_file.clone()),
                    self.strategy_less_fact(left_factors[1-li].clone(), right_factors[1-ri].clone(), lt.line_file.clone()),
                ]);
            }
        }
        if alts.is_empty() { return Ok(None); }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.try_strategy_requirement_alternatives(alts, verify_state)?
        else { return Ok(None); };
        Ok(Some(CommonPositiveFactorLessStrategySingleStep { requirement_facts, proof_of_requirement_facts }))
    }
}

fn as_lt(fact: &AtomicFact) -> Option<&LessFact> {
    match fact { AtomicFact::LessFact(f) => Some(f), _ => None }
}
fn as_add(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_sub(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_mul(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_div(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => Some((x.left.as_ref().clone(), x.right.as_ref().clone())), _ => None }
}
fn as_pow(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => Some((x.base.as_ref().clone(), x.exponent.as_ref().clone())), _ => None }
}
fn as_abs(obj: &Obj) -> Option<Obj> {
    match obj { Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref().clone()), _ => None }
}
fn pow_obj(base: Obj, exponent: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base: Box::new(base), exponent: Box::new(exponent) }))
}
fn zero_lt_mul(fact: &AtomicFact) -> Option<(Obj, Obj, Option<SourceLine>)> {
    let lt = as_lt(fact)?;
    if !is_zero_obj(&lt.left) { return None; }
    let (l, r) = as_mul(&lt.right)?;
    Some((l, r, lt.line_file.clone()))
}
fn zero_lt_div(fact: &AtomicFact) -> Option<(Obj, Obj, Option<SourceLine>)> {
    let lt = as_lt(fact)?;
    if !is_zero_obj(&lt.left) { return None; }
    let (l, r) = as_div(&lt.right)?;
    Some((l, r, lt.line_file.clone()))
}
