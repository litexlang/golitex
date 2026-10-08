use super::verify_trig_interval_bound::TrigIntervalBoundSide;
use crate::ast::fact::{AtomicFact, EqualFact, Fact, LessEqualFact, LessFact};
use crate::ast::obj::{
    Arccos, Arccot, Arcsin, Arctan, ArithmeticOperator, Cos, Cot, Div, Literal, Number, Obj, Pi,
    Sin, Tan, TrigOperator,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin SinArcsinLeftInverse: sin(arcsin(x)) = x on the arcsin domain.
// Mathematical property: principal left inverse of sin.
// Example: with (-1) <= x <= 1, prove sin(arcsin(x)) = x.
pub struct SinArcsinLeftInverseBuiltinRuleProof {}

// Builtin CosArccosLeftInverse: cos(arccos(x)) = x on the arccos domain.
// Mathematical property: principal left inverse of cos.
// Example: with (-1) <= x <= 1, prove cos(arccos(x)) = x.
pub struct CosArccosLeftInverseBuiltinRuleProof {}

// Builtin TanArctanLeftInverse: tan(arctan(x)) = x for x R.
// Mathematical property: principal left inverse of tan.
// Example: prove tan(arctan(x)) = x.
pub struct TanArctanLeftInverseBuiltinRuleProof {}

// Builtin CotArccotLeftInverse: cot(arccot(x)) = x for x R.
// Mathematical property: principal left inverse of cot.
// Example: prove cot(arccot(x)) = x.
pub struct CotArccotLeftInverseBuiltinRuleProof {}

// Builtin ArcsinSinRightInverse: arcsin(sin(y)) = y on [-pi/2, pi/2].
// Mathematical property: principal right inverse of sin.
// Example: with (-pi)/2 <= y <= pi/2, prove arcsin(sin(y)) = y.
pub struct ArcsinSinRightInverseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ArccosCosRightInverse: arccos(cos(y)) = y on [0, pi].
// Mathematical property: principal right inverse of cos.
// Example: with 0 <= y <= pi, prove arccos(cos(y)) = y.
pub struct ArccosCosRightInverseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ArctanTanRightInverse: arctan(tan(y)) = y on (-pi/2, pi/2).
// Mathematical property: principal right inverse of tan.
// Example: with (-pi)/2 < y < pi/2, prove arctan(tan(y)) = y.
pub struct ArctanTanRightInverseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ArccotCotRightInverse: arccot(cot(y)) = y on (0, pi).
// Mathematical property: principal right inverse of cot (range (0, pi)).
// Example: with 0 < y < pi, prove arccot(cot(y)) = y.
pub struct ArccotCotRightInverseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ArcsinExactZero: arcsin(0) = 0.
// Mathematical property: principal branch at 0.
// Example: prove arcsin(0) = 0.
pub struct ArcsinExactZeroBuiltinRuleProof {}

// Builtin ArcsinExactOne: arcsin(1) = pi / 2.
// Mathematical property: principal branch at the right endpoint.
// Example: prove arcsin(1) = pi / 2.
pub struct ArcsinExactOneBuiltinRuleProof {}

// Builtin ArcsinExactNegOne: arcsin(-1) = (-pi) / 2.
// Mathematical property: principal branch at the left endpoint.
// Example: prove arcsin(-1) = (-pi) / 2.
pub struct ArcsinExactNegOneBuiltinRuleProof {}

// Builtin ArccosExactOne: arccos(1) = 0.
// Example: prove arccos(1) = 0.
pub struct ArccosExactOneBuiltinRuleProof {}

// Builtin ArccosExactZero: arccos(0) = pi / 2.
// Example: prove arccos(0) = pi / 2.
pub struct ArccosExactZeroBuiltinRuleProof {}

// Builtin ArccosExactNegOne: arccos(-1) = pi.
// Example: prove arccos(-1) = pi.
pub struct ArccosExactNegOneBuiltinRuleProof {}

// Builtin ArctanExactZero: arctan(0) = 0.
// Example: prove arctan(0) = 0.
pub struct ArctanExactZeroBuiltinRuleProof {}

// Builtin ArccotExactZero: arccot(0) = pi / 2.
// Example: prove arccot(0) = pi / 2.
pub struct ArccotExactZeroBuiltinRuleProof {}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_inverse_trig(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InverseTrigEqualityBuiltinRuleProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(proof) = self.try_left_inverse_trig_equality(left, right)? {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.try_right_inverse_trig_equality(left, right, fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) = try_exact_inverse_trig_equality(left, right) {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    fn try_left_inverse_trig_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<InverseTrigEqualityBuiltinRuleProof>> {
        match left {
            Obj::TrigOperator(TrigOperator::Sin(Sin { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg: inner })) = arg.as_ref()
                {
                    if inner.ir() == right.ir() {
                        return Ok(Some(
                            InverseTrigEqualityBuiltinRuleProof::SinArcsinLeftInverse(
                                SinArcsinLeftInverseBuiltinRuleProof {},
                            ),
                        ));
                    }
                }
            }
            Obj::TrigOperator(TrigOperator::Cos(Cos { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg: inner })) = arg.as_ref()
                {
                    if inner.ir() == right.ir() {
                        return Ok(Some(
                            InverseTrigEqualityBuiltinRuleProof::CosArccosLeftInverse(
                                CosArccosLeftInverseBuiltinRuleProof {},
                            ),
                        ));
                    }
                }
            }
            Obj::TrigOperator(TrigOperator::Tan(Tan { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Arctan(Arctan { arg: inner })) = arg.as_ref()
                {
                    if inner.ir() == right.ir() {
                        return Ok(Some(
                            InverseTrigEqualityBuiltinRuleProof::TanArctanLeftInverse(
                                TanArctanLeftInverseBuiltinRuleProof {},
                            ),
                        ));
                    }
                }
            }
            Obj::TrigOperator(TrigOperator::Cot(Cot { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Arccot(Arccot { arg: inner })) = arg.as_ref()
                {
                    if inner.ir() == right.ir() {
                        return Ok(Some(
                            InverseTrigEqualityBuiltinRuleProof::CotArccotLeftInverse(
                                CotArccotLeftInverseBuiltinRuleProof {},
                            ),
                        ));
                    }
                }
            }
            _ => {}
        }
        Ok(None)
    }

    fn try_right_inverse_trig_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InverseTrigEqualityBuiltinRuleProof>> {
        let child_state = verify_state;
        match left {
            Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Sin(Sin { arg: inner })) = arg.as_ref() {
                    if inner.ir() == right.ir() {
                        let proofs = self.verify_closed_interval_premises(
                            right,
                            &negative_half_pi(),
                            &half_pi(),
                            fact,
                            child_state,
                        )?;
                        if let Some(proof_of_requirement_facts) = proofs {
                            return Ok(Some(
                                InverseTrigEqualityBuiltinRuleProof::ArcsinSinRightInverse(
                                    ArcsinSinRightInverseBuiltinRuleProof {
                                        proof_of_requirement_facts,
                                    },
                                ),
                            ));
                        }
                    }
                }
            }
            Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Cos(Cos { arg: inner })) = arg.as_ref() {
                    if inner.ir() == right.ir() {
                        let proofs = self.verify_closed_interval_premises(
                            right,
                            &zero_obj(),
                            &pi_obj(),
                            fact,
                            child_state,
                        )?;
                        if let Some(proof_of_requirement_facts) = proofs {
                            return Ok(Some(
                                InverseTrigEqualityBuiltinRuleProof::ArccosCosRightInverse(
                                    ArccosCosRightInverseBuiltinRuleProof {
                                        proof_of_requirement_facts,
                                    },
                                ),
                            ));
                        }
                    }
                }
            }
            Obj::TrigOperator(TrigOperator::Arctan(Arctan { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Tan(Tan { arg: inner })) = arg.as_ref() {
                    if inner.ir() == right.ir() {
                        let proofs = self.verify_open_interval_premises(
                            right,
                            &negative_half_pi(),
                            &half_pi(),
                            fact,
                            child_state,
                        )?;
                        if let Some(proof_of_requirement_facts) = proofs {
                            return Ok(Some(
                                InverseTrigEqualityBuiltinRuleProof::ArctanTanRightInverse(
                                    ArctanTanRightInverseBuiltinRuleProof {
                                        proof_of_requirement_facts,
                                    },
                                ),
                            ));
                        }
                    }
                }
            }
            Obj::TrigOperator(TrigOperator::Arccot(Arccot { arg })) => {
                if let Obj::TrigOperator(TrigOperator::Cot(Cot { arg: inner })) = arg.as_ref() {
                    if inner.ir() == right.ir() {
                        let proofs = self.verify_open_interval_premises(
                            right,
                            &zero_obj(),
                            &pi_obj(),
                            fact,
                            child_state,
                        )?;
                        if let Some(proof_of_requirement_facts) = proofs {
                            return Ok(Some(
                                InverseTrigEqualityBuiltinRuleProof::ArccotCotRightInverse(
                                    ArccotCotRightInverseBuiltinRuleProof {
                                        proof_of_requirement_facts,
                                    },
                                ),
                            ));
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(None)
    }

    pub(super) fn verify_closed_interval_premises(
        &mut self,
        value: &Obj,
        lower: &Obj,
        upper: &Obj,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<Vec<VerifyFactResult>>> {
        let lo: Fact = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: lower.clone(),
            right: value.clone(),
            line_file: fact.line_file.clone(),
        })
        .into();
        let hi: Fact = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.clone(),
            right: upper.clone(),
            line_file: fact.line_file.clone(),
        })
        .into();
        let Some(lo_proof) = self.verify_trig_interval_bound(
            &lo,
            TrigIntervalBoundSide::Lower,
            verify_state.clone(),
        )?
        else {
            return Ok(None);
        };
        let Some(hi_proof) =
            self.verify_trig_interval_bound(&hi, TrigIntervalBoundSide::Upper, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(vec![lo_proof, hi_proof]))
    }

    fn verify_open_interval_premises(
        &mut self,
        value: &Obj,
        lower: &Obj,
        upper: &Obj,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<Vec<VerifyFactResult>>> {
        let lo: Fact = AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: lower.clone(),
            right: value.clone(),
            line_file: fact.line_file.clone(),
        })
        .into();
        let hi: Fact = AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: value.clone(),
            right: upper.clone(),
            line_file: fact.line_file.clone(),
        })
        .into();
        let mut lo_proof = self.verify_trig_interval_bound(
            &lo,
            TrigIntervalBoundSide::Lower,
            verify_state.clone(),
        )?;
        // The first quadrant is contained in arctan's principal interval.
        // Keep the actual stronger 0<x fact instead of fabricating -pi/2<x.
        // This fixed containment does not introduce general bound search.
        if lo_proof.is_none() && lower.ir() == negative_half_pi().ir() {
            let positive: Fact = LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: zero_obj(),
                right: value.clone(),
                line_file: fact.line_file.clone(),
            }
            .into();
            lo_proof = self.verify_trig_interval_bound(
                &positive,
                TrigIntervalBoundSide::Lower,
                verify_state.clone(),
            )?;
        }
        let Some(lo_proof) = lo_proof else {
            return Ok(None);
        };
        let Some(hi_proof) =
            self.verify_trig_interval_bound(&hi, TrigIntervalBoundSide::Upper, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(vec![lo_proof, hi_proof]))
    }
}

// Local match helper before mapping onto EqualitySearchProofByBuiltinRule.
pub enum InverseTrigEqualityBuiltinRuleProof {
    SinArcsinLeftInverse(SinArcsinLeftInverseBuiltinRuleProof),
    CosArccosLeftInverse(CosArccosLeftInverseBuiltinRuleProof),
    TanArctanLeftInverse(TanArctanLeftInverseBuiltinRuleProof),
    CotArccotLeftInverse(CotArccotLeftInverseBuiltinRuleProof),
    ArcsinSinRightInverse(ArcsinSinRightInverseBuiltinRuleProof),
    ArccosCosRightInverse(ArccosCosRightInverseBuiltinRuleProof),
    ArctanTanRightInverse(ArctanTanRightInverseBuiltinRuleProof),
    ArccotCotRightInverse(ArccotCotRightInverseBuiltinRuleProof),
    ArcsinExactZero(ArcsinExactZeroBuiltinRuleProof),
    ArcsinExactOne(ArcsinExactOneBuiltinRuleProof),
    ArcsinExactNegOne(ArcsinExactNegOneBuiltinRuleProof),
    ArccosExactOne(ArccosExactOneBuiltinRuleProof),
    ArccosExactZero(ArccosExactZeroBuiltinRuleProof),
    ArccosExactNegOne(ArccosExactNegOneBuiltinRuleProof),
    ArctanExactZero(ArctanExactZeroBuiltinRuleProof),
    ArccotExactZero(ArccotExactZeroBuiltinRuleProof),
}

fn try_exact_inverse_trig_equality(
    left: &Obj,
    right: &Obj,
) -> Option<InverseTrigEqualityBuiltinRuleProof> {
    match left {
        Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg }))
            if is_number(arg, "0") && is_number(right, "0") =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArcsinExactZero(
                ArcsinExactZeroBuiltinRuleProof {},
            ))
        }
        Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg }))
            if is_number(arg, "1") && objs_match_half_pi_bound(right, &half_pi()) =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArcsinExactOne(
                ArcsinExactOneBuiltinRuleProof {},
            ))
        }
        Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg }))
            if is_number(arg, "-1") && objs_match_half_pi_bound(right, &negative_half_pi()) =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArcsinExactNegOne(
                ArcsinExactNegOneBuiltinRuleProof {},
            ))
        }
        Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg }))
            if is_number(arg, "1") && is_number(right, "0") =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArccosExactOne(
                ArccosExactOneBuiltinRuleProof {},
            ))
        }
        Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg }))
            if is_number(arg, "0") && objs_match_half_pi_bound(right, &half_pi()) =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArccosExactZero(
                ArccosExactZeroBuiltinRuleProof {},
            ))
        }
        Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg }))
            if is_number(arg, "-1") && objs_match_half_pi_bound(right, &pi_obj()) =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArccosExactNegOne(
                ArccosExactNegOneBuiltinRuleProof {},
            ))
        }
        Obj::TrigOperator(TrigOperator::Arctan(Arctan { arg }))
            if is_number(arg, "0") && is_number(right, "0") =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArctanExactZero(
                ArctanExactZeroBuiltinRuleProof {},
            ))
        }
        Obj::TrigOperator(TrigOperator::Arccot(Arccot { arg }))
            if is_number(arg, "0") && objs_match_half_pi_bound(right, &half_pi()) =>
        {
            Some(InverseTrigEqualityBuiltinRuleProof::ArccotExactZero(
                ArccotExactZeroBuiltinRuleProof {},
            ))
        }
        _ => None,
    }
}

pub(crate) fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}

pub(crate) fn pi_obj() -> Obj {
    Obj::Literal(Literal::Pi(Pi))
}

pub(crate) fn half_pi() -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(pi_obj()),
        right: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: "2".to_string(),
        }))),
    }))
}

pub(crate) fn negative_half_pi() -> Obj {
    // Parse shape of `-pi / 2`: `(-pi) / 2` = Div(Neg(pi), 2).
    Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(Obj::ArithmeticOperator(ArithmeticOperator::Neg(
            crate::ast::obj::Neg {
                arg: Box::new(pi_obj()),
            },
        ))),
        right: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: "2".to_string(),
        }))),
    }))
}

pub(crate) fn objs_match_half_pi_bound(left: &Obj, right: &Obj) -> bool {
    use crate::rational_expression::objs_equal_by_rational_expression_evaluation;
    objs_equal_by_rational_expression_evaluation(left, right)
}

fn is_number(obj: &Obj, expected: &str) -> bool {
    use crate::rational_expression::objs_equal_by_rational_expression_evaluation;
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == expected
    ) || objs_equal_by_rational_expression_evaluation(
        obj,
        &Obj::Literal(Literal::Number(Number {
            normalized_value: expected.to_string(),
        })),
    )
}
