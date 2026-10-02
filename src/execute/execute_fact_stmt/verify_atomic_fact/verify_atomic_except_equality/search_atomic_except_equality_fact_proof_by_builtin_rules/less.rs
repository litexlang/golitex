use super::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::{AtomicFact, Fact, LessFact};
use crate::ast::obj::{Add, ArithmeticOperator, Mul, Obj, Sub, TrigOperator};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{is_zero_obj, zero_obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromPositiveLiteralBoundBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::is_number_value;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::trig_bounds::{
    match_arccot_principal_lower, match_arccot_principal_upper, match_arctan_principal_lower,
    match_arctan_principal_upper,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::runtime::FactId;

// Builtin rules for `a < b`.
pub enum LessFactSearchProofByBuiltinRule {
    // Converse order, citing an existing opposite-direction comparison.
    FromKnownGreater(FromKnownGreaterBuiltinRuleProof),
    FromKnownOrderComplement(FromKnownOrderComplementBuiltinRuleProof),
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L < R,
    // then `left < right`.
    // Examples: `1 < 2`, `1 + 1 < 5`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Subtract-one is strictly below the minuend.
    // Mathematical property: for any object `x`, `x - 1 < x`.
    // Example: prove `n - 1 < n` (used by inductive recursive domain checks).
    SubtractOneLess(SubtractOneLessBuiltinRuleProof),
    // Arctan principal lower bound: `-pi/2 < arctan(x)`.
    // Example: prove `-pi / 2 < arctan(x)`.
    ArctanPrincipalLowerBound(ArctanPrincipalLowerBoundBuiltinRuleProof),
    // Arctan principal upper bound: `arctan(x) < pi/2`.
    // Example: prove `arctan(x) < pi / 2`.
    ArctanPrincipalUpperBound(ArctanPrincipalUpperBoundBuiltinRuleProof),
    // Arccot principal lower bound: `0 < arccot(x)` (range (0, pi)).
    // Example: prove `0 < arccot(x)`.
    ArccotPrincipalLowerBound(ArccotPrincipalLowerBoundBuiltinRuleProof),
    // Arccot principal upper bound: `arccot(x) < pi`.
    // Example: prove `arccot(x) < pi`.
    ArccotPrincipalUpperBound(ArccotPrincipalUpperBoundBuiltinRuleProof),
    // Sum of positives: `0 < a` and `0 < b` ⇒ `0 < a + b`.
    // Example: known `0 < x`, `0 < y` prove `0 < x + y`.
    SumBothPositive(SumBothPositiveBuiltinRuleProof),
    // Mixed sum positivity (left strict): `0 < a` and `0 <= b` ⇒ `0 < a + b`.
    // Example: known `0 < x`, `0 <= y` prove `0 < x + y`.
    SumLeftStrictRightNonnegative(SumLeftStrictRightNonnegativeBuiltinRuleProof),
    // Mixed sum positivity (right strict): `0 <= a` and `0 < b` ⇒ `0 < a + b`.
    SumLeftNonnegativeRightStrict(SumLeftNonnegativeRightStrictBuiltinRuleProof),
    // Product of positives: `0 < a` and `0 < b` ⇒ `0 < a * b`.
    // Example: known `0 < x`, `0 < y` prove `0 < x * y`.
    ProductBothPositive(ProductBothPositiveBuiltinRuleProof),
    // Even integer power is positive from a nonzero base: `a != 0` ⇒ `0 < a^(2k)` / `0 < a * a`.
    // Example: known `x != 0` proves `0 < x^2`.
    EvenPowPositiveFromNonzero(EvenPowPositiveFromNonzeroBuiltinRuleProof),
    // Positive base power is positive: `0 < a` ⇒ `0 < a^b`.
    // Example: known `0 < a` proves `0 < a^n`.
    PowPositiveFromPositiveBase(PowPositiveFromPositiveBaseBuiltinRuleProof),
    // Square root is positive: `0 < x` ⇒ `0 < sqrt(x)`.
    // Example: known `0 < x` proves `0 < sqrt(x)`.
    SqrtPositive(SqrtPositiveBuiltinRuleProof),
    // Square root is strictly monotone: `0 <= a`, `0 <= b`, `a < b` ⇒ `sqrt(a) < sqrt(b)`.
    SqrtMonotoneIncreasing(SqrtMonotoneIncreasingBuiltinRuleProof),
    // Log with base > 1 preserves strict order on positive args.
    // Example: known `1 < 2`, `0 < x`, `0 < y`, `x < y` prove `log(2, x) < log(2, y)`.
    LogOrderPreservingStrict(LogOrderPreservingStrictBuiltinRuleProof),
    // Log sign: `1 < a` and `1 < x` ⇒ `0 < log(a, x)`.
    LogPositiveFromBaseAndArgGtOne(LogPositiveFromBaseAndArgGtOneBuiltinRuleProof),
    // Log sign: `1 < a`, `0 < x`, `x < 1` ⇒ `log(a, x) < 0`.
    LogNegativeFromBaseGtOneArgInUnitInterval(LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof),
    // Order transitivity with at least one strict premise.
    // Example: known `x <= y` and `y < z` prove `x < z`.
    LessTransitivity(LessTransitivityBuiltinRuleProof),
    // Subtraction bridge: known `0 < b - a` prove `a < b`.
    // Example: known `0 < y - x` proves `x < y`.
    LessFromPosDifference(LessFromPosDifferenceBuiltinRuleProof),
    // Subtraction bridge: known `a < b` prove `0 < b - a`.
    // Example: known `x < y` proves `0 < y - x`.
    PosDifferenceFromLess(PosDifferenceFromLessBuiltinRuleProof),
    // Mod remainder upper bound: `a $in Z`, `b $in N+` ⇒ `a % b < b`.
    // Example: after `have a Z` and `have b N+`, prove `a % b < b`.
    ModRemainderStrictUpperBound(ModRemainderStrictUpperBoundBuiltinRuleProof),
    // Positive common divisor preserves strict order.
    // Example: known `0 < c` and `a < b` prove `a / c < b / c`.
    DivMonotoneStrictSamePosDivisor(DivMonotoneStrictSamePosDivisorBuiltinRuleProof),
    // Dividing a positive quantity by a factor > 1 shrinks it.
    // Example: known `0 < a` and `1 < b` prove `a / b < a`.
    DivByGtOneLessSelf(DivByGtOneLessSelfBuiltinRuleProof),

    // Negative common divisor reverses strict order.
    // Mathematical property: `c < 0` and `b < a` ⇒ `a / c < b / c`.
    // Example: known `c < 0` and `y < x` prove `x / c < y / c`.
    DivMonotoneStrictSameNegDivisor(DivMonotoneStrictSameNegDivisorBuiltinRuleProof),
    // Weaken a known numeric lower bound to a smaller literal strict goal.
    // Example: known `4 < x` proves `2 < x`.
    NumericLowerBoundWeakenLt(NumericLowerBoundWeakenLtBuiltinRuleProof),
    // Weaken a known numeric upper bound to a larger literal strict goal.
    // Example: known `x < 4` proves `x < 6`.
    NumericUpperBoundWeakenLt(NumericUpperBoundWeakenLtBuiltinRuleProof),
    // Positive even integer exceeds one.
    // Mathematical property: `i $in N+` and `i % 2 = 0` ⇒ `1 < i`.
    // Example: after `have i N+` and `trust i % 2 = 0`, prove `1 < i`.
    PositiveEvenGtOne(PositiveEvenGtOneBuiltinRuleProof),
    // Right addend congruence (strict): `a < b` ⇒ `a + c < b + c`.
    // Example: known `x < y` proves `x + 1 < y + 1`.
    AddRightCongruenceStrict(AddRightCongruenceStrictBuiltinRuleProof),
    // Left addend congruence (strict): `a < b` ⇒ `c + a < c + b`.
    // Example: known `x < y` proves `1 + x < 1 + y`.
    AddLeftCongruenceStrict(AddLeftCongruenceStrictBuiltinRuleProof),
    // Left multiplication by a positive factor preserves strict order.
    // Mathematical property: `0 < k` and `a < b` ⇒ `k * a < k * b`.
    // Example: known `0 < 2` and `x < y` prove `2 * x < 2 * y`.
    MulLeftPositiveMonotoneStrict(MulLeftPositiveMonotoneStrictBuiltinRuleProof),
    // Right multiplication by a positive factor preserves strict order.
    // Example: known `0 < c` and `a < b` prove `a * c < b * c`.
    MulRightPositiveMonotoneStrict(MulRightPositiveMonotoneStrictBuiltinRuleProof),
    // Sign from a known positive literal lower bound.
    // Example: known `a >= 1` proves `0 < a`.
    OrderSignFromPositiveLiteralBound(OrderSignFromPositiveLiteralBoundBuiltinRuleProof),
    // Order flip: `(-1)*x < 0` from known `x > 0`.
    // Example: trust a > 0; (-1) * a < 0.
    OrderFlipMulMinusOne(OrderFlipMulMinusOneToLessBuiltinRuleProof),
    // Finite A ⊊ B implies |A| < |B|.
    FiniteSetSizeProperSubsetLt(FiniteSetSizeProperSubsetLtBuiltinRuleProof),
}

// Payload: both evaluated normals with left_normal < right_normal.
pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct FiniteSetSizeProperSubsetLtBuiltinRuleProof {
    pub inclusion_proof: FiniteProperInclusionProof,
}

pub enum FiniteProperInclusionProof {
    ByProperSubset {
        proper_subset_proof: VerifyFactResult,
    },
    BySubsetAndNotEqual {
        subset_proof: VerifyFactResult,
        not_equal_proof: VerifyFactResult,
    },
}

// Payload: the minuend `x` in the goal `x - 1 < x`.
pub struct SubtractOneLessBuiltinRuleProof {
    pub minuend: Obj,
}

pub struct ArctanPrincipalLowerBoundBuiltinRuleProof {}
pub struct ArctanPrincipalUpperBoundBuiltinRuleProof {}
pub struct ArccotPrincipalLowerBoundBuiltinRuleProof {}
pub struct ArccotPrincipalUpperBoundBuiltinRuleProof {}

pub struct SumBothPositiveBuiltinRuleProof {
    pub left_positive_proof: VerifyFactResult,
    pub right_positive_proof: VerifyFactResult,
}

pub struct SumLeftStrictRightNonnegativeBuiltinRuleProof {
    pub left_positive_proof: VerifyFactResult,
    pub right_nonnegative_proof: VerifyFactResult,
}

pub struct SumLeftNonnegativeRightStrictBuiltinRuleProof {
    pub left_nonnegative_proof: VerifyFactResult,
    pub right_positive_proof: VerifyFactResult,
}

pub struct ProductBothPositiveBuiltinRuleProof {
    pub left_positive_proof: VerifyFactResult,
    pub right_positive_proof: VerifyFactResult,
}

pub struct EvenPowPositiveFromNonzeroBuiltinRuleProof {
    pub base_nonzero_proof: VerifyFactResult,
}

pub struct PowPositiveFromPositiveBaseBuiltinRuleProof {
    pub base_positive_proof: VerifyFactResult,
}

pub struct SqrtPositiveBuiltinRuleProof {
    pub arg_positive_proof: VerifyFactResult,
}

pub struct SqrtMonotoneIncreasingBuiltinRuleProof {
    pub left_nonnegative_proof: VerifyFactResult,
    pub right_nonnegative_proof: VerifyFactResult,
    pub args_order_proof: VerifyFactResult,
}

pub struct LogOrderPreservingStrictBuiltinRuleProof {
    pub base_gt_one_proof: VerifyFactResult,
    pub left_arg_positive_proof: VerifyFactResult,
    pub right_arg_positive_proof: VerifyFactResult,
    pub args_order_proof: VerifyFactResult,
}

pub struct LogPositiveFromBaseAndArgGtOneBuiltinRuleProof {
    pub base_gt_one_proof: VerifyFactResult,
    pub arg_gt_one_proof: VerifyFactResult,
}

pub struct LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof {
    pub base_gt_one_proof: VerifyFactResult,
    pub arg_positive_proof: VerifyFactResult,
    pub arg_lt_one_proof: VerifyFactResult,
}

pub struct LessTransitivityBuiltinRuleProof {
    pub left_to_mid_cite_fact_id: FactId,
    pub mid_to_right_cite_fact_id: FactId,
    pub left_to_mid_strict: bool,
    pub mid_to_right_strict: bool,
}

pub struct LessFromPosDifferenceBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

pub struct PosDifferenceFromLessBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

pub struct ModRemainderStrictUpperBoundBuiltinRuleProof {
    pub dividend_in_z_proof: VerifyFactResult,
    pub modulus_in_n_pos_proof: VerifyFactResult,
}

pub struct DivMonotoneStrictSamePosDivisorBuiltinRuleProof {
    pub divisor_pos_proof: VerifyFactResult,
    pub numerators_order_proof: VerifyFactResult,
}

pub struct DivByGtOneLessSelfBuiltinRuleProof {
    pub numerator_pos_proof: VerifyFactResult,
    pub denominator_gt_one_proof: VerifyFactResult,
}




pub struct DivMonotoneStrictSameNegDivisorBuiltinRuleProof {
    pub divisor_neg_proof: VerifyFactResult,
    pub numerators_order_proof: VerifyFactResult,
}

pub struct NumericLowerBoundWeakenLtBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct NumericUpperBoundWeakenLtBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct PositiveEvenGtOneBuiltinRuleProof {
    pub in_n_pos_proof: VerifyFactResult,
    pub even_proof: VerifyFactResult,
}

pub struct AddRightCongruenceStrictBuiltinRuleProof {
    pub premise_proof: VerifyFactResult,
}

pub struct AddLeftCongruenceStrictBuiltinRuleProof {
    pub premise_proof: VerifyFactResult,
}

pub struct MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub positive_factor_proof: VerifyFactResult,
    pub order_premise_proof: VerifyFactResult,
}

pub struct MulRightPositiveMonotoneStrictBuiltinRuleProof {
    pub positive_factor_proof: VerifyFactResult,
    pub order_premise_proof: VerifyFactResult,
}


pub struct FromKnownGreaterBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

impl Runtime {
    // Builtin search for `a < b`.
    // B0: none (no known-cite / reflexivity for strict < here).
    // A: match on Obj shapes of (left, right).
    // B1: closed decimal evaluation.
    // Example: prove `n - 1 < n`, `-pi/2 < arctan(x)`, or `1 < 2`.
    pub fn search_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if let Some(premise_proof) = self.known_greater_proof(&fact.right, &fact.left) {
            return Ok(Some(LessFactSearchProofByBuiltinRule::FromKnownGreater(FromKnownGreaterBuiltinRuleProof { premise_proof })));
        }
        if let Some(proof) = self.known_order_complement(fact.clone().into(), verify_state.clone())? {
            return Ok(Some(LessFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof)));
        }
        if let Some(proof) = self.try_order_sign_from_positive_literal_bound(fact) {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::OrderSignFromPositiveLiteralBound(proof),
            ));
        }
        if let Some(proof) = self.try_order_flip_mul_minus_one_to_less(fact) {
            return Ok(Some(LessFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(
                proof,
            )));
        }

        // Zero-premise closed numeric (no nested search).
        if let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        {
            if cmp == NumberCompareResult::Less {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ClosedNumericComparison(
                        ClosedNumericComparisonBuiltinRuleProof {
                            left_normal,
                            right_normal,
                        },
                    ),
                ));
            }
        }

        // Pure shape cites that do not nest verify_fact.
        match (&fact.left, &fact.right) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
                minuend,
            ) if is_number_value(right.as_ref(), "1") && left.as_ref().ir() == minuend.ir() => {
                return Ok(Some(LessFactSearchProofByBuiltinRule::SubtractOneLess(
                    SubtractOneLessBuiltinRuleProof {
                        minuend: left.as_ref().clone(),
                    },
                )));
            }
            (_, Obj::TrigOperator(TrigOperator::Arctan(_)))
                if match_arctan_principal_lower(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArctanPrincipalLowerBound(
                        ArctanPrincipalLowerBoundBuiltinRuleProof {},
                    ),
                ));
            }
            (Obj::TrigOperator(TrigOperator::Arctan(_)), _)
                if match_arctan_principal_upper(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArctanPrincipalUpperBound(
                        ArctanPrincipalUpperBoundBuiltinRuleProof {},
                    ),
                ));
            }
            (_, Obj::TrigOperator(TrigOperator::Arccot(_)))
                if match_arccot_principal_lower(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArccotPrincipalLowerBound(
                        ArccotPrincipalLowerBoundBuiltinRuleProof {},
                    ),
                ));
            }
            (Obj::TrigOperator(TrigOperator::Arccot(_)), _)
                if match_arccot_principal_upper(&fact.left, &fact.right) =>
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::ArccotPrincipalUpperBound(
                        ArccotPrincipalUpperBoundBuiltinRuleProof {},
                    ),
                ));
            }
            _ => {}
        }

        if !verify_state.can_use_builtin_rule {
            return Ok(None);
        }
        let verify_state = verify_state.clone();

        match (&fact.left, &fact.right) {
            // `0 < a + b` / `0 < a * b`
            (left, Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left: a, right: b })))
                if is_zero_obj(left) =>
            {
                if let Some(proof) = self.sum_positive_cone_proof(
                    a.as_ref(),
                    b.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }
            (left, Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left: a, right: b })))
                if is_zero_obj(left) =>
            {
                if let Some(proof) = self.product_both_positive_proof(
                    a.as_ref(),
                    b.as_ref(),
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
            }

            // Both Add: strict congruence on shared addend.
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
                    if let Some(proof) = self.add_right_congruence_strict_proof(
                        left_l.as_ref(),
                        right_l.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
                if left_l.as_ref().ir() == right_l.as_ref().ir() {
                    if let Some(proof) = self.add_left_congruence_strict_proof(
                        left_r.as_ref(),
                        right_r.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
            }

            // Both Mul: positive-factor monotone strict.
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
                    if let Some(proof) = self.mul_left_positive_monotone_strict_proof(
                        left_l.as_ref(),
                        left_r.as_ref(),
                        right_r.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
                if left_r.as_ref().ir() == right_r.as_ref().ir() {
                    if let Some(proof) = self.mul_right_positive_monotone_strict_proof(
                        left_l.as_ref(),
                        right_l.as_ref(),
                        left_r.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
            }

            _ => {}
        }

        if let Some(proof) =
            self.search_order_power_sqrt_log_less_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_order_div_mod_bridge_trans_less_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_order_stage_a_remainder_less_proof(fact, verify_state)?
        {
            return Ok(Some(proof));
        }

        Ok(None)
    }


    // Prefer both-strict, then left-strict/right-weak, then left-weak/right-strict.
    fn sum_positive_cone_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let left_pos = self.verify_positive(left, verify_state.clone())?;
        let right_pos = self.verify_positive(right, verify_state.clone())?;
        if !left_pos.is_failed() && !right_pos.is_failed() {
            return Ok(Some(LessFactSearchProofByBuiltinRule::SumBothPositive(
                SumBothPositiveBuiltinRuleProof {
                    left_positive_proof: left_pos,
                    right_positive_proof: right_pos,
                },
            )));
        }
        let left_pos = self.verify_positive(left, verify_state.clone())?;
        let right_nonneg = self.verify_nonnegative_for_less(right, verify_state.clone())?;
        if !left_pos.is_failed() && !right_nonneg.is_failed() {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::SumLeftStrictRightNonnegative(
                    SumLeftStrictRightNonnegativeBuiltinRuleProof {
                        left_positive_proof: left_pos,
                        right_nonnegative_proof: right_nonneg,
                    },
                ),
            ));
        }
        let left_nonneg = self.verify_nonnegative_for_less(left, verify_state.clone())?;
        let right_pos = self.verify_positive(right, verify_state)?;
        if !left_nonneg.is_failed() && !right_pos.is_failed() {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::SumLeftNonnegativeRightStrict(
                    SumLeftNonnegativeRightStrictBuiltinRuleProof {
                        left_nonnegative_proof: left_nonneg,
                        right_positive_proof: right_pos,
                    },
                ),
            ));
        }
        Ok(None)
    }

    fn product_both_positive_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let left_positive_proof = self.verify_positive(left, verify_state.clone())?;
        if left_positive_proof.is_failed() {
            return Ok(None);
        }
        let right_positive_proof = self.verify_positive(right, verify_state)?;
        if right_positive_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LessFactSearchProofByBuiltinRule::ProductBothPositive(
            ProductBothPositiveBuiltinRuleProof {
                left_positive_proof,
                right_positive_proof,
            },
        )))
    }

    pub(crate) fn verify_positive(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero_obj(),
            right: obj.clone(),
            line_file: None,
        }));
        self.verify_builtin_rule_premise(&goal, verify_state)
    }

    fn verify_nonnegative_for_less(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        // Reuse the shared `0 <= obj` goal helper from order_abs via verify_fact.
        let goal = Fact::AtomicFact(AtomicFact::LessEqualFact(
            crate::ast::fact::LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: zero_obj(),
                right: obj.clone(),
                line_file: None,
            },
        ));
        self.verify_builtin_rule_premise(&goal, verify_state)
    }

    fn add_right_congruence_strict_proof(
        &mut self,
        left_l: &Obj,
        right_l: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let premise = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_l.clone(),
            right: right_l.clone(),
            line_file: None,
        }));
        let premise_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::AddRightCongruenceStrict(
                AddRightCongruenceStrictBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    fn add_left_congruence_strict_proof(
        &mut self,
        left_r: &Obj,
        right_r: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let premise = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_r.clone(),
            right: right_r.clone(),
            line_file: None,
        }));
        let premise_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::AddLeftCongruenceStrict(
                AddLeftCongruenceStrictBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    fn mul_left_positive_monotone_strict_proof(
        &mut self,
        k: &Obj,
        left_a: &Obj,
        right_b: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let positive_factor_proof = self.verify_positive(k, verify_state.clone())?;
        if positive_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_a.clone(),
            right: right_b.clone(),
            line_file: None,
        }));
        let order_premise_proof = self.verify_builtin_rule_premise(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::MulLeftPositiveMonotoneStrict(
                MulLeftPositiveMonotoneStrictBuiltinRuleProof {
                    positive_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }

    fn mul_right_positive_monotone_strict_proof(
        &mut self,
        left_a: &Obj,
        right_b: &Obj,
        k: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let positive_factor_proof = self.verify_positive(k, verify_state.clone())?;
        if positive_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_a.clone(),
            right: right_b.clone(),
            line_file: None,
        }));
        let order_premise_proof = self.verify_builtin_rule_premise(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::MulRightPositiveMonotoneStrict(
                MulRightPositiveMonotoneStrictBuiltinRuleProof {
                    positive_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }
}
