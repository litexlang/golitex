//! Real trigonometric interval sign/order laws, with bounded inherited premises.
use super::less::LessFactSearchProofByBuiltinRule;
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{Fact, LessFact, LessEqualFact, GreaterFact, GreaterEqualFact};
use crate::ast::obj::{Obj, TrigOperator, ArithmeticOperator, Neg, Mul, Sub, Literal, Number};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{zero_obj, pi_obj, half_pi, negative_half_pi};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::verify_trig_interval_bound::trig_interval_bound_spellings;
use crate::runtime::{Runtime, RuntimeResult};

// -pi/2 < x < pi/2 => 0 < cos(x). Enclosing WD checks real arguments and partial operators.
pub struct CosPositiveOnOpenHalfPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
}
impl CosPositiveOnOpenHalfPiProof {
    pub fn new(lower_bound: VerifyFactResult, upper_bound: VerifyFactResult) -> Self {
        Self {
            lower_bound,
            upper_bound,
        }
    }
}

// -pi < x < 0 => sin(x) < 0. Enclosing WD checks real arguments and partial operators.
pub struct SinNegativeOnOpenNegativePiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
}
impl SinNegativeOnOpenNegativePiProof {
    pub fn new(lower_bound: VerifyFactResult, upper_bound: VerifyFactResult) -> Self {
        Self {
            lower_bound,
            upper_bound,
        }
    }
}

// -pi/2 < x < 0 => tan(x) < 0. Enclosing WD checks real arguments and partial operators.
pub struct TanNegativeOnOpenNegativeHalfPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
}
impl TanNegativeOnOpenNegativeHalfPiProof {
    pub fn new(lower_bound: VerifyFactResult, upper_bound: VerifyFactResult) -> Self {
        Self {
            lower_bound,
            upper_bound,
        }
    }
}

// pi/2 < x < pi => cot(x) < 0. Enclosing WD checks real arguments and partial operators.
pub struct CotNegativeOnOpenUpperHalfPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
}
impl CotNegativeOnOpenUpperHalfPiProof {
    pub fn new(lower_bound: VerifyFactResult, upper_bound: VerifyFactResult) -> Self {
        Self {
            lower_bound,
            upper_bound,
        }
    }
}

// 0 < x < pi/2 => 0 < sin(x). Enclosing WD checks real arguments and partial operators.
pub struct SinPositiveOnFirstQuadrantProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
}
impl SinPositiveOnFirstQuadrantProof {
    pub fn new(lower_bound: VerifyFactResult, upper_bound: VerifyFactResult) -> Self {
        Self {
            lower_bound,
            upper_bound,
        }
    }
}

// 0 < x < pi/2 => 0 < cos(x). Enclosing WD checks real arguments and partial operators.
pub struct CosPositiveOnFirstQuadrantProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
}
impl CosPositiveOnFirstQuadrantProof {
    pub fn new(lower_bound: VerifyFactResult, upper_bound: VerifyFactResult) -> Self {
        Self {
            lower_bound,
            upper_bound,
        }
    }
}

// 0 <= a < b <= pi => cos(b) < cos(a). Enclosing WD checks real arguments and partial operators.
pub struct CosStrictDecreasingOnClosedPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}
impl CosStrictDecreasingOnClosedPiProof {
    pub fn new(
        lower_bound: VerifyFactResult,
        upper_bound: VerifyFactResult,
        argument_order: VerifyFactResult,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
            argument_order,
        }
    }
}

// -pi/2 < a < b < pi/2 => tan(a) < tan(b). Enclosing WD checks real arguments and partial operators.
pub struct TanStrictIncreasingOnOpenHalfPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}
impl TanStrictIncreasingOnOpenHalfPiProof {
    pub fn new(
        lower_bound: VerifyFactResult,
        upper_bound: VerifyFactResult,
        argument_order: VerifyFactResult,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
            argument_order,
        }
    }
}

// 0 < a < b < pi => cot(b) < cot(a). Enclosing WD checks real arguments and partial operators.
pub struct CotStrictDecreasingOnOpenPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}
impl CotStrictDecreasingOnOpenPiProof {
    pub fn new(
        lower_bound: VerifyFactResult,
        upper_bound: VerifyFactResult,
        argument_order: VerifyFactResult,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
            argument_order,
        }
    }
}

// -pi/2 <= a <= b <= pi/2 => sin(a) <= sin(b). Enclosing WD checks real arguments and partial operators.
pub struct SinWeakIncreasingOnClosedHalfPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}
impl SinWeakIncreasingOnClosedHalfPiProof {
    pub fn new(
        lower_bound: VerifyFactResult,
        upper_bound: VerifyFactResult,
        argument_order: VerifyFactResult,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
            argument_order,
        }
    }
}

// 0 <= a <= b <= pi => cos(b) <= cos(a). Enclosing WD checks real arguments and partial operators.
pub struct CosWeakDecreasingOnClosedPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}
impl CosWeakDecreasingOnClosedPiProof {
    pub fn new(
        lower_bound: VerifyFactResult,
        upper_bound: VerifyFactResult,
        argument_order: VerifyFactResult,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
            argument_order,
        }
    }
}

// -pi/2 < a <= b < pi/2 => tan(a) <= tan(b). Enclosing WD checks real arguments and partial operators.
pub struct TanWeakIncreasingOnOpenHalfPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}
impl TanWeakIncreasingOnOpenHalfPiProof {
    pub fn new(
        lower_bound: VerifyFactResult,
        upper_bound: VerifyFactResult,
        argument_order: VerifyFactResult,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
            argument_order,
        }
    }
}

// 0 < a <= b < pi => cot(b) <= cot(a). Enclosing WD checks real arguments and partial operators.
pub struct CotWeakDecreasingOnOpenPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}
impl CotWeakDecreasingOnOpenPiProof {
    pub fn new(
        lower_bound: VerifyFactResult,
        upper_bound: VerifyFactResult,
        argument_order: VerifyFactResult,
    ) -> Self {
        Self {
            lower_bound,
            upper_bound,
            argument_order,
        }
    }
}

impl Runtime {
    // Fixed interval laws, not an expansion search. Existing sine and first-quadrant
    // tan/cot handlers run first. Example: -pi/2<x<pi/2 => 0<cos(x).
    pub(super) fn search_additional_trig_less(
        &mut self,
        fact: &LessFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if fact.left.ir() == zero_obj().ir() {
            if let Obj::TrigOperator(TrigOperator::Cos(value)) = &fact.right {
                if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                    &value.arg,
                    &value.arg,
                    &negative_half_pi(),
                    &half_pi(),
                    false,
                    state,
                )? {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::CosPositiveOnOpenHalfPi(
                            CosPositiveOnOpenHalfPiProof::new(lower_bound, upper_bound),
                        ),
                    ));
                }
            }
        }
        if fact.right.ir() == zero_obj().ir() {
            if let Obj::TrigOperator(TrigOperator::Sin(value)) = &fact.left {
                if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                    &value.arg,
                    &value.arg,
                    &negative_pi(),
                    &zero_obj(),
                    false,
                    state,
                )? {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::SinNegativeOnOpenNegativePi(
                            SinNegativeOnOpenNegativePiProof::new(lower_bound, upper_bound),
                        ),
                    ));
                }
            }
        }
        if fact.right.ir() == zero_obj().ir() {
            if let Obj::TrigOperator(TrigOperator::Tan(value)) = &fact.left {
                if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                    &value.arg,
                    &value.arg,
                    &negative_half_pi(),
                    &zero_obj(),
                    false,
                    state,
                )? {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::TanNegativeOnOpenNegativeHalfPi(
                            TanNegativeOnOpenNegativeHalfPiProof::new(lower_bound, upper_bound),
                        ),
                    ));
                }
            }
        }
        if fact.right.ir() == zero_obj().ir() {
            if let Obj::TrigOperator(TrigOperator::Cot(value)) = &fact.left {
                if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                    &value.arg,
                    &value.arg,
                    &half_pi(),
                    &pi_obj(),
                    false,
                    state,
                )? {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::CotNegativeOnOpenUpperHalfPi(
                            CotNegativeOnOpenUpperHalfPiProof::new(lower_bound, upper_bound),
                        ),
                    ));
                }
            }
        }
        if fact.left.ir() == zero_obj().ir() {
            if let Obj::TrigOperator(TrigOperator::Sin(value)) = &fact.right {
                if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                    &value.arg,
                    &value.arg,
                    &zero_obj(),
                    &half_pi(),
                    false,
                    state,
                )? {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::SinPositiveOnFirstQuadrant(
                            SinPositiveOnFirstQuadrantProof::new(lower_bound, upper_bound),
                        ),
                    ));
                }
            }
        }
        if fact.left.ir() == zero_obj().ir() {
            if let Obj::TrigOperator(TrigOperator::Cos(value)) = &fact.right {
                if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                    &value.arg,
                    &value.arg,
                    &zero_obj(),
                    &half_pi(),
                    false,
                    state,
                )? {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::CosPositiveOnFirstQuadrant(
                            CosPositiveOnFirstQuadrantProof::new(lower_bound, upper_bound),
                        ),
                    ));
                }
            }
        }
        if let (Obj::TrigOperator(TrigOperator::Cos(a)), Obj::TrigOperator(TrigOperator::Cos(b))) =
            (&fact.right, &fact.left)
        {
            if let Some((lower_bound, upper_bound)) =
                self.additional_trig_bounds(&a.arg, &b.arg, &zero_obj(), &pi_obj(), true, state)?
            {
                if let Some(argument_order) =
                    self.additional_trig_comparison(&a.arg, &b.arg, false, state)?
                {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::CosStrictDecreasingOnClosedPi(
                            CosStrictDecreasingOnClosedPiProof::new(
                                lower_bound,
                                upper_bound,
                                argument_order,
                            ),
                        ),
                    ));
                }
            }
        }
        if let (Obj::TrigOperator(TrigOperator::Tan(a)), Obj::TrigOperator(TrigOperator::Tan(b))) =
            (&fact.left, &fact.right)
        {
            if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                &a.arg,
                &b.arg,
                &negative_half_pi(),
                &half_pi(),
                false,
                state,
            )? {
                if let Some(argument_order) =
                    self.additional_trig_comparison(&a.arg, &b.arg, false, state)?
                {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::TanStrictIncreasingOnOpenHalfPi(
                            TanStrictIncreasingOnOpenHalfPiProof::new(
                                lower_bound,
                                upper_bound,
                                argument_order,
                            ),
                        ),
                    ));
                }
            }
        }
        if let (Obj::TrigOperator(TrigOperator::Cot(a)), Obj::TrigOperator(TrigOperator::Cot(b))) =
            (&fact.right, &fact.left)
        {
            if let Some((lower_bound, upper_bound)) =
                self.additional_trig_bounds(&a.arg, &b.arg, &zero_obj(), &pi_obj(), false, state)?
            {
                if let Some(argument_order) =
                    self.additional_trig_comparison(&a.arg, &b.arg, false, state)?
                {
                    return Ok(Some(
                        LessFactSearchProofByBuiltinRule::CotStrictDecreasingOnOpenPi(
                            CotStrictDecreasingOnOpenPiProof::new(
                                lower_bound,
                                upper_bound,
                                argument_order,
                            ),
                        ),
                    ));
                }
            }
        }
        Ok(None)
    }

    // Closed sine/cosine and open tangent/cotangent intervals preserve weak
    // order in the indicated direction. Strict premises may justify weak order.
    pub(super) fn search_additional_trig_less_equal(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if let (Obj::TrigOperator(TrigOperator::Sin(a)), Obj::TrigOperator(TrigOperator::Sin(b))) =
            (&fact.left, &fact.right)
        {
            if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                &a.arg,
                &b.arg,
                &negative_half_pi(),
                &half_pi(),
                true,
                state,
            )? {
                if let Some(argument_order) =
                    self.additional_trig_comparison(&a.arg, &b.arg, true, state)?
                {
                    return Ok(Some(
                        LessEqualFactSearchProofByBuiltinRule::SinWeakIncreasingOnClosedHalfPi(
                            SinWeakIncreasingOnClosedHalfPiProof::new(
                                lower_bound,
                                upper_bound,
                                argument_order,
                            ),
                        ),
                    ));
                }
            }
        }
        if let (Obj::TrigOperator(TrigOperator::Cos(a)), Obj::TrigOperator(TrigOperator::Cos(b))) =
            (&fact.right, &fact.left)
        {
            if let Some((lower_bound, upper_bound)) =
                self.additional_trig_bounds(&a.arg, &b.arg, &zero_obj(), &pi_obj(), true, state)?
            {
                if let Some(argument_order) =
                    self.additional_trig_comparison(&a.arg, &b.arg, true, state)?
                {
                    return Ok(Some(
                        LessEqualFactSearchProofByBuiltinRule::CosWeakDecreasingOnClosedPi(
                            CosWeakDecreasingOnClosedPiProof::new(
                                lower_bound,
                                upper_bound,
                                argument_order,
                            ),
                        ),
                    ));
                }
            }
        }
        if let (Obj::TrigOperator(TrigOperator::Tan(a)), Obj::TrigOperator(TrigOperator::Tan(b))) =
            (&fact.left, &fact.right)
        {
            if let Some((lower_bound, upper_bound)) = self.additional_trig_bounds(
                &a.arg,
                &b.arg,
                &negative_half_pi(),
                &half_pi(),
                false,
                state,
            )? {
                if let Some(argument_order) =
                    self.additional_trig_comparison(&a.arg, &b.arg, true, state)?
                {
                    return Ok(Some(
                        LessEqualFactSearchProofByBuiltinRule::TanWeakIncreasingOnOpenHalfPi(
                            TanWeakIncreasingOnOpenHalfPiProof::new(
                                lower_bound,
                                upper_bound,
                                argument_order,
                            ),
                        ),
                    ));
                }
            }
        }
        if let (Obj::TrigOperator(TrigOperator::Cot(a)), Obj::TrigOperator(TrigOperator::Cot(b))) =
            (&fact.right, &fact.left)
        {
            if let Some((lower_bound, upper_bound)) =
                self.additional_trig_bounds(&a.arg, &b.arg, &zero_obj(), &pi_obj(), false, state)?
            {
                if let Some(argument_order) =
                    self.additional_trig_comparison(&a.arg, &b.arg, true, state)?
                {
                    return Ok(Some(
                        LessEqualFactSearchProofByBuiltinRule::CotWeakDecreasingOnOpenPi(
                            CotWeakDecreasingOnOpenPiProof::new(
                                lower_bound,
                                upper_bound,
                                argument_order,
                            ),
                        ),
                    ));
                }
            }
        }
        Ok(None)
    }

    // Lower then upper: each returned child is the actual written comparison,
    // including a reversed spelling or a strict premise used for a weak bound.
    fn additional_trig_bounds(
        &mut self,
        left_arg: &Obj,
        right_arg: &Obj,
        lower: &Obj,
        upper: &Obj,
        closed: bool,
        state: VerifyState,
    ) -> RuntimeResult<Option<(VerifyFactResult, VerifyFactResult)>> {
        let mut lower_bound = None;
        for spelling in additional_bound_spellings(lower) {
            if let Some(proof) =
                self.additional_trig_comparison(&spelling, left_arg, closed, state)?
            {
                lower_bound = Some(proof);
                break;
            }
        }
        let Some(lower_bound) = lower_bound else {
            return Ok(None);
        };
        for spelling in additional_bound_spellings(upper) {
            if let Some(upper_bound) =
                self.additional_trig_comparison(right_arg, &spelling, closed, state)?
            {
                return Ok(Some((lower_bound, upper_bound)));
            }
        }
        Ok(None)
    }

    // Weak first, then strict; canonical then converse. The builtin dispatcher
    // supplied this premise state: do not reset it or enter another builtin layer.
    fn additional_trig_comparison(
        &mut self,
        left: &Obj,
        right: &Obj,
        weak: bool,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        for strict in if weak { vec![false, true] } else { vec![true] } {
            for reverse in [false, true] {
                let fact_id = self.global_ids.allocate_fact_id();
                let premise: Fact = match (strict, reverse) {
                    (true, false) => LessFact {
                        fact_id,
                        left: left.clone(),
                        right: right.clone(),
                        line_file: None,
                    }
                    .into(),
                    (true, true) => GreaterFact {
                        fact_id,
                        left: right.clone(),
                        right: left.clone(),
                        line_file: None,
                    }
                    .into(),
                    (false, false) => LessEqualFact {
                        fact_id,
                        left: left.clone(),
                        right: right.clone(),
                        line_file: None,
                    }
                    .into(),
                    (false, true) => GreaterEqualFact {
                        fact_id,
                        left: right.clone(),
                        right: left.clone(),
                        line_file: None,
                    }
                    .into(),
                };
                let proof = self.verify_builtin_rule_premise(&premise, state)?;
                if !proof.is_failed() {
                    return Ok(Some(proof));
                }
            }
        }
        Ok(None)
    }
}

fn negative_pi() -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
        arg: Box::new(pi_obj()),
    }))
}

// Fixed negative constants only. Angles are never symbolically normalized.
fn additional_bound_spellings(bound: &Obj) -> Vec<Obj> {
    if bound.ir() == negative_pi().ir() {
        vec![
            bound.clone(),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: Box::new(Obj::Literal(Literal::Number(Number {
                    normalized_value: "-1".to_string(),
                }))),
                right: Box::new(pi_obj()),
            })),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                left: Box::new(zero_obj()),
                right: Box::new(pi_obj()),
            })),
        ]
    } else {
        trig_interval_bound_spellings(bound)
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/trig_additional_interval_order/tests.rs"]
mod trig_additional_interval_order_tests;
