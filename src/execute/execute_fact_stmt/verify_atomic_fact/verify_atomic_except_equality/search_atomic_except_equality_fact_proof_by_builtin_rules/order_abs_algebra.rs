//! Order / absolute-value algebra builtins for `<=`.
//!
//! Each matcher is a dedicated LessEqual builtin rule (one rule ↔ one proof struct).
//! Subgoals are proved via `verify_fact` (known facts, closed numeric, earlier rules).

use crate::ast::fact::{AtomicFact, Fact, LessEqualFact};
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Mul, Obj, Sub, TrigOperator,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::trig_bounds::{
    match_arccos_principal_lower, match_arccos_principal_upper, match_arcsin_principal_lower,
    match_arcsin_principal_upper, match_unit_circle_lower, match_unit_circle_upper,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{
    is_zero_obj, zero_obj, AbsLeFromSymmetricBoundsBuiltinRuleProof,
    AbsLeImpliesNegUpperBuiltinRuleProof, AbsLeImpliesUpperBuiltinRuleProof,
    AbsNonnegativeBuiltinRuleProof, AbsSelfLowerBuiltinRuleProof, AbsSelfUpperBuiltinRuleProof,
    AbsReverseTriangleAddBuiltinRuleProof, AbsReverseTriangleSubBuiltinRuleProof,
    AbsTriangleInequalityBuiltinRuleProof, AddLeftCongruenceBuiltinRuleProof,
    AddLeftNonnegativeBuiltinRuleProof, AddRightCongruenceBuiltinRuleProof,
    AddRightNonnegativeBuiltinRuleProof, ArccosPrincipalLowerBoundBuiltinRuleProof,
    ArccosPrincipalUpperBoundBuiltinRuleProof, ArcsinPrincipalLowerBoundBuiltinRuleProof,
    ArcsinPrincipalUpperBoundBuiltinRuleProof,
    LessEqualFactSearchProofByBuiltinRule, MulLeftNonnegativeMonotoneBuiltinRuleProof,
    MulRightNonnegativeMonotoneBuiltinRuleProof, ProductOfNonnegativesBuiltinRuleProof,
    SubNonnegativeBuiltinRuleProof, SumOfNonnegativesBuiltinRuleProof,
    UnitCircleLowerBoundBuiltinRuleProof, UnitCircleUpperBoundBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{FactId, Runtime, RuntimeResult};

impl Runtime {
    // Shape dispatch for `a <= b` algebra / abs / trig builtins.
    // Match on Obj constructors of (left, right); nested if only after entering a variant.
    // Example: `x <= x + c`, `abs(x+y) <= abs(x)+abs(y)`, `-pi/2 <= arcsin(x)`.
    pub(super) fn search_order_abs_algebra_less_equal_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        match (&fact.left, &fact.right) {
            // Both Add: congruence on shared addend.
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: left_l,
                    right: left_r,
                })),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: right_l,
                    right: right_r,
                })),
            ) => {
                if left_r.as_ref().ir() == right_r.as_ref().ir() {
                    return self.add_right_congruence_from_addends(
                        left_l.as_ref(),
                        right_l.as_ref(),
                        verify_state,
                    );
                }
                if left_l.as_ref().ir() == right_l.as_ref().ir() {
                    return self.add_left_congruence_from_addends(
                        left_r.as_ref(),
                        right_r.as_ref(),
                        verify_state,
                    );
                }
                Ok(None)
            }

            // Both Mul: monotone in the free factor.
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: left_l,
                    right: left_r,
                })),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: right_l,
                    right: right_r,
                })),
            ) => {
                if left_l.as_ref().ir() == right_l.as_ref().ir() {
                    return self.mul_left_nonnegative_monotone_from_factors(
                        left_l.as_ref(),
                        left_r.as_ref(),
                        right_r.as_ref(),
                        verify_state,
                    );
                }
                if left_r.as_ref().ir() == right_r.as_ref().ir() {
                    return self.mul_right_nonnegative_monotone_from_factors(
                        left_l.as_ref(),
                        right_l.as_ref(),
                        left_r.as_ref(),
                        verify_state,
                    );
                }
                Ok(None)
            }

            // Left Abs / right Add: triangle inequality `abs(x+y) <= abs(x)+abs(y)`.
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: _sum })),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: abs_x,
                    right: abs_y,
                })),
            ) if abs_triangle_inequality_matches(fact) => Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::AbsTriangleInequality(
                    AbsTriangleInequalityBuiltinRuleProof {},
                ),
            )),

            // Left Sub(Abs,Abs) / right Abs(Add|Sub): reverse triangle.
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(_)),
            ) if matches!(
                (left.as_ref(), right.as_ref()),
                (
                    Obj::ArithmeticOperator(ArithmeticOperator::Abs(_)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Abs(_)),
                )
            ) =>
            {
                if abs_reverse_triangle_add_matches(fact) {
                    return Ok(Some(
                        LessEqualFactSearchProofByBuiltinRule::AbsReverseTriangleAdd(
                            AbsReverseTriangleAddBuiltinRuleProof {},
                        ),
                    ));
                }
                if abs_reverse_triangle_sub_matches(fact) {
                    return Ok(Some(
                        LessEqualFactSearchProofByBuiltinRule::AbsReverseTriangleSub(
                            AbsReverseTriangleSubBuiltinRuleProof {},
                        ),
                    ));
                }
                Ok(None)
            }

            // Left Abs: sandwich upper bound.
            (Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })), _) => {
                self.abs_le_from_symmetric_bounds_proof(fact, verify_state)
            }

            // Right Abs: `x <= abs(x)`.
            (_, Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })))
                if fact.left.ir() == arg.as_ref().ir() =>
            {
                Ok(Some(LessEqualFactSearchProofByBuiltinRule::AbsSelfUpper(
                    AbsSelfUpperBuiltinRuleProof {},
                )))
            }

            // Right Add: `a <= a+b` or `a <= b+a` (only when left matches an addend).
            // Non-matching goals such as `0 <= u + v` fall through to the left-zero arm.
            (
                left,
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left: a, right: b })),
            ) if left.ir() == a.as_ref().ir() || left.ir() == b.as_ref().ir() => {
                if left.ir() == a.as_ref().ir() {
                    return self.add_right_nonnegative_from_addend(b.as_ref(), verify_state);
                }
                self.add_left_nonnegative_from_addend(a.as_ref(), verify_state)
            }

            // Left Sub: `a-b <= a`, or `-abs(x) <= x`.
            (Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })), right_obj) => {
                if left.as_ref().ir() == right_obj.ir() {
                    return self.sub_nonnegative_from_subtrahend(right.as_ref(), verify_state);
                }
                if is_zero_obj(left.as_ref()) {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) =
                        right.as_ref()
                    {
                        if arg.as_ref().ir() == right_obj.ir() {
                            return Ok(Some(LessEqualFactSearchProofByBuiltinRule::AbsSelfLower(
                                AbsSelfLowerBuiltinRuleProof {},
                            )));
                        }
                    }
                }
                Ok(None)
            }

            // Left zero: `0 <= abs(x)`, `0 <= a+b`, `0 <= a*b`, or `0 <= n` from `n $in N`.
            (left, right) if is_zero_obj(left) => {
                if matches!(
                    right,
                    Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))
                ) {
                    return Ok(Some(LessEqualFactSearchProofByBuiltinRule::AbsNonnegative(
                        AbsNonnegativeBuiltinRuleProof {},
                    )));
                }
                if let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: a,
                    right: b,
                })) = right
                {
                    return self.sum_of_nonnegatives_proof(a.as_ref(), b.as_ref(), verify_state);
                }
                if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: a,
                    right: b,
                })) = right
                {
                    return self.product_of_nonnegatives_proof(a.as_ref(), b.as_ref(), verify_state);
                }
                Ok(None)
            }

            // Trig principal / unit-circle bounds.
            (_, Obj::TrigOperator(TrigOperator::Arcsin(_)))
                if match_arcsin_principal_lower(&fact.left, &fact.right) =>
            {
                Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::ArcsinPrincipalLowerBound(
                        ArcsinPrincipalLowerBoundBuiltinRuleProof {},
                    ),
                ))
            }
            (Obj::TrigOperator(TrigOperator::Arcsin(_)), _)
                if match_arcsin_principal_upper(&fact.left, &fact.right) =>
            {
                Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::ArcsinPrincipalUpperBound(
                        ArcsinPrincipalUpperBoundBuiltinRuleProof {},
                    ),
                ))
            }
            (_, Obj::TrigOperator(TrigOperator::Arccos(_)))
                if match_arccos_principal_lower(&fact.left, &fact.right) =>
            {
                Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::ArccosPrincipalLowerBound(
                        ArccosPrincipalLowerBoundBuiltinRuleProof {},
                    ),
                ))
            }
            (Obj::TrigOperator(TrigOperator::Arccos(_)), _)
                if match_arccos_principal_upper(&fact.left, &fact.right) =>
            {
                Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::ArccosPrincipalUpperBound(
                        ArccosPrincipalUpperBoundBuiltinRuleProof {},
                    ),
                ))
            }
            (
                _,
                Obj::TrigOperator(TrigOperator::Sin(_) | TrigOperator::Cos(_)),
            ) if match_unit_circle_lower(&fact.left, &fact.right) => Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::UnitCircleLowerBound(
                    UnitCircleLowerBoundBuiltinRuleProof {},
                ),
            )),
            (
                Obj::TrigOperator(TrigOperator::Sin(_) | TrigOperator::Cos(_)),
                _,
            ) if match_unit_circle_upper(&fact.left, &fact.right) => Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::UnitCircleUpperBound(
                    UnitCircleUpperBoundBuiltinRuleProof {},
                ),
            )),

            _ => Ok(None),
        }
    }

    // `a <= a + b` from `0 <= b`.
    fn add_right_nonnegative_from_addend(
        &mut self,
        addend: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let proof = self.verify_nonnegative(addend, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AddRightNonnegative(
                AddRightNonnegativeBuiltinRuleProof {
                    nonnegative_addend_proof: proof,
                },
            ),
        ))
    }

    // `a <= b + a` from `0 <= b`.
    fn add_left_nonnegative_from_addend(
        &mut self,
        addend: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let proof = self.verify_nonnegative(addend, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AddLeftNonnegative(
                AddLeftNonnegativeBuiltinRuleProof {
                    nonnegative_addend_proof: proof,
                },
            ),
        ))
    }

    fn add_right_congruence_from_addends(
        &mut self,
        left_l: &Obj,
        right_l: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let premise = less_equal_fact(left_l, right_l, self);
        let premise_proof = self.verify_fact(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AddRightCongruence(
                AddRightCongruenceBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    fn add_left_congruence_from_addends(
        &mut self,
        left_r: &Obj,
        right_r: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let premise = less_equal_fact(left_r, right_r, self);
        let premise_proof = self.verify_fact(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AddLeftCongruence(
                AddLeftCongruenceBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    fn sub_nonnegative_from_subtrahend(
        &mut self,
        subtrahend: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let proof = self.verify_nonnegative(subtrahend, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LessEqualFactSearchProofByBuiltinRule::SubNonnegative(
            SubNonnegativeBuiltinRuleProof {
                nonnegative_subtrahend_proof: proof,
            },
        )))
    }

    fn mul_left_nonnegative_monotone_from_factors(
        &mut self,
        k: &Obj,
        left_a: &Obj,
        right_b: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let nonnegative_factor_proof = self.verify_nonnegative(k, verify_state.clone())?;
        if nonnegative_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = less_equal_fact(left_a, right_b, self);
        let order_premise_proof = self.verify_fact(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::MulLeftNonnegativeMonotone(
                MulLeftNonnegativeMonotoneBuiltinRuleProof {
                    nonnegative_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }

    fn mul_right_nonnegative_monotone_from_factors(
        &mut self,
        left_a: &Obj,
        right_b: &Obj,
        k: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let nonnegative_factor_proof = self.verify_nonnegative(k, verify_state.clone())?;
        if nonnegative_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = less_equal_fact(left_a, right_b, self);
        let order_premise_proof = self.verify_fact(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::MulRightNonnegativeMonotone(
                MulRightNonnegativeMonotoneBuiltinRuleProof {
                    nonnegative_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }

    // `x <= a` and `-x <= a` ⇒ `abs(x) <= a`.
    fn abs_le_from_symmetric_bounds_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) = &fact.left else {
            return Ok(None);
        };
        let bound = &fact.right;
        let upper = less_equal_fact(arg.as_ref(), bound, self);
        let upper_proof = self.verify_fact(&upper, verify_state.clone())?;
        if upper_proof.is_failed() {
            return Ok(None);
        }
        let neg_x = negate_obj(arg.as_ref());
        let neg_upper = less_equal_fact(&neg_x, bound, self);
        let neg_upper_proof = self.verify_fact(&neg_upper, verify_state)?;
        if neg_upper_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AbsLeFromSymmetricBounds(
                AbsLeFromSymmetricBoundsBuiltinRuleProof {
                    upper_proof,
                    neg_upper_proof,
                },
            ),
        ))
    }

    // Known `abs(x) <= a` ⇒ goal `x <= a`.
    pub(super) fn abs_le_implies_upper_proof(
        &mut self,
        fact: &LessEqualFact,
    ) -> Option<LessEqualFactSearchProofByBuiltinRule> {
        let abs_x = abs_obj(&fact.left);
        let premise_proof = self.known_less_equal_proof(&abs_x, &fact.right)?;
        Some(LessEqualFactSearchProofByBuiltinRule::AbsLeImpliesUpper(
            AbsLeImpliesUpperBuiltinRuleProof { premise_proof },
        ))
    }

    // Known `abs(x) <= a` ⇒ goal `-x <= a`.
    pub(super) fn abs_le_implies_neg_upper_proof(
        &mut self,
        fact: &LessEqualFact,
    ) -> Option<LessEqualFactSearchProofByBuiltinRule> {
        let x = match_negation(&fact.left)?;
        let abs_x = abs_obj(x);
        let premise_proof = self.known_less_equal_proof(&abs_x, &fact.right)?;
        Some(LessEqualFactSearchProofByBuiltinRule::AbsLeImpliesNegUpper(
            AbsLeImpliesNegUpperBuiltinRuleProof { premise_proof },
        ))
    }

    // `0 <= a + b` from `0 <= a` and `0 <= b`.
    fn sum_of_nonnegatives_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let left_nonnegative_proof = self.verify_nonnegative(left, verify_state.clone())?;
        if left_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let right_nonnegative_proof = self.verify_nonnegative(right, verify_state)?;
        if right_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(
                SumOfNonnegativesBuiltinRuleProof {
                    left_nonnegative_proof,
                    right_nonnegative_proof,
                },
            ),
        ))
    }

    // `0 <= a * b` from `0 <= a` and `0 <= b`.
    fn product_of_nonnegatives_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let left_nonnegative_proof = self.verify_nonnegative(left, verify_state.clone())?;
        if left_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        let right_nonnegative_proof = self.verify_nonnegative(right, verify_state)?;
        if right_nonnegative_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::ProductOfNonnegatives(
                ProductOfNonnegativesBuiltinRuleProof {
                    left_nonnegative_proof,
                    right_nonnegative_proof,
                },
            ),
        ))
    }

    fn verify_nonnegative(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult>
    {
        let goal = less_equal_fact(&zero_obj(), obj, self);
        self.verify_fact(&goal, verify_state)
    }


}

fn less_equal_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

fn negate_obj(obj: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(zero_obj()),
        right: Box::new(obj.clone()),
    }))
}

fn abs_obj(obj: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
        arg: Box::new(obj.clone()),
    }))
}

fn match_negation(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) =>
        {
            Some(right.as_ref())
        }
        _ => None,
    }
}

fn abs_self_upper_matches(fact: &LessEqualFact) -> bool {
    matches!(
        &fact.right,
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg }))
            if arg.as_ref().ir() == fact.left.ir()
    )
}

fn abs_self_lower_matches(fact: &LessEqualFact) -> bool {
    let Some(abs_x) = (match &fact.left {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) =>
        {
            match right.as_ref() {
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
                _ => None,
            }
        }
        _ => None,
    }) else {
        return false;
    };
    abs_x.ir() == fact.right.ir()
}

fn abs_triangle_inequality_matches(fact: &LessEqualFact) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: sum })) = &fact.left else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left: x, right: y })) = sum.as_ref()
    else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: abs_x,
        right: abs_y,
    })) = &fact.right
    else {
        return false;
    };
    matches!(
        (abs_x.as_ref(), abs_y.as_ref()),
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: ax })),
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: ay })),
        ) if ax.as_ref().ir() == x.as_ref().ir() && ay.as_ref().ir() == y.as_ref().ir()
    )
}

fn abs_reverse_triangle_add_matches(fact: &LessEqualFact) -> bool {
    abs_reverse_triangle_matches(fact, true)
}

fn abs_reverse_triangle_sub_matches(fact: &LessEqualFact) -> bool {
    abs_reverse_triangle_matches(fact, false)
}

// Goal `abs(x) - abs(y) <= abs(x ± y)`.
fn abs_reverse_triangle_matches(fact: &LessEqualFact, use_add: bool) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = &fact.left else {
        return false;
    };
    let (
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: x })),
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: y })),
    ) = (left.as_ref(), right.as_ref())
    else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: combo })) = &fact.right else {
        return false;
    };
    if use_add {
        matches!(
            combo.as_ref(),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left: a, right: b }))
                if a.as_ref().ir() == x.as_ref().ir() && b.as_ref().ir() == y.as_ref().ir()
        )
    } else {
        matches!(
            combo.as_ref(),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left: a, right: b }))
                if a.as_ref().ir() == x.as_ref().ir() && b.as_ref().ir() == y.as_ref().ir()
        )
    }
}
