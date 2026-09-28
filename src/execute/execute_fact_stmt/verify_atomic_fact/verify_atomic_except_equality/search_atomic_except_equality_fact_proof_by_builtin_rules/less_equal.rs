use crate::ast::fact::LessEqualFact;
use crate::ast::obj::{Literal, Number, Obj};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `a <= b`.
pub enum LessEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L <= R,
    // then `left <= right`.
    // Examples: `1 <= 2`, `2 <= 2`, `1 + 1 <= 3`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Order reflexivity: `x <= x`.
    // Mathematical property: <= is reflexive on any object.
    // Example: prove `a <= a`.
    OrderReflexivity(OrderReflexivityBuiltinRuleProof),
    // Strict order implies weak order.
    // Mathematical property: `a < b` ⇒ `a <= b`.
    // Example: known `x < 0` proves `x <= 0`.
    FromKnownLess(FromKnownLessBuiltinRuleProof),
    // Natural membership implies non-negative.
    // Mathematical property: `n $in N` ⇒ `0 <= n`.
    // Example: after `have n N`, prove `0 <= n`.
    FromKnownInNatural(FromKnownInNaturalBuiltinRuleProof),
    // Arcsin principal lower bound: `-pi/2 <= arcsin(x)` on the arcsin domain.
    // Example: after `(-1) <= x <= 1`, prove `-pi / 2 <= arcsin(x)`.
    ArcsinPrincipalLowerBound(ArcsinPrincipalLowerBoundBuiltinRuleProof),
    // Arcsin principal upper bound: `arcsin(x) <= pi/2`.
    // Example: prove `arcsin(x) <= pi / 2`.
    ArcsinPrincipalUpperBound(ArcsinPrincipalUpperBoundBuiltinRuleProof),
    // Arccos principal lower bound: `0 <= arccos(x)`.
    // Example: prove `0 <= arccos(x)`.
    ArccosPrincipalLowerBound(ArccosPrincipalLowerBoundBuiltinRuleProof),
    // Arccos principal upper bound: `arccos(x) <= pi`.
    // Example: prove `arccos(x) <= pi`.
    ArccosPrincipalUpperBound(ArccosPrincipalUpperBoundBuiltinRuleProof),
    // Unit-circle lower bound: `-1 <= sin(x)` or `-1 <= cos(x)`.
    // Example: prove `-1 <= sin(x)`.
    UnitCircleLowerBound(UnitCircleLowerBoundBuiltinRuleProof),
    // Unit-circle upper bound: `sin(x) <= 1` or `cos(x) <= 1`.
    // Example: prove `cos(x) <= 1`.
    UnitCircleUpperBound(UnitCircleUpperBoundBuiltinRuleProof),
    // Absolute value is nonnegative: `0 <= abs(x)`.
    // Mathematical property: for every real `x`, `abs(x) >= 0`.
    // Example: prove `0 <= abs(a)`.
    AbsNonnegative(AbsNonnegativeBuiltinRuleProof),
    // Right translation by a nonnegative addend: `a <= a + b` from `0 <= b`.
    // Mathematical property: adding a nonnegative quantity does not decrease.
    // Example: known `0 <= c` proves `x <= x + c`.
    AddRightNonnegative(AddRightNonnegativeBuiltinRuleProof),
    // Left translation by a nonnegative addend: `a <= b + a` from `0 <= b`.
    // Example: known `0 <= c` proves `x <= c + x`.
    AddLeftNonnegative(AddLeftNonnegativeBuiltinRuleProof),
    // Right addend congruence: `a <= b` ⇒ `a + c <= b + c`.
    // Example: known `x <= y` proves `x + 1 <= y + 1`.
    AddRightCongruence(AddRightCongruenceBuiltinRuleProof),
    // Left addend congruence: `a <= b` ⇒ `c + a <= c + b`.
    // Example: known `x <= y` proves `1 + x <= 1 + y`.
    AddLeftCongruence(AddLeftCongruenceBuiltinRuleProof),
    // Subtract a nonnegative: `a - b <= a` from `0 <= b`.
    // Example: known `0 <= c` proves `x - c <= x`.
    SubNonnegative(SubNonnegativeBuiltinRuleProof),
    // Left multiplication by a nonnegative: `0 <= k` and `a <= b` ⇒ `k * a <= k * b`.
    // Example: known `0 <= 2` and `x <= y` prove `2 * x <= 2 * y`.
    MulLeftNonnegativeMonotone(MulLeftNonnegativeMonotoneBuiltinRuleProof),
    // Right multiplication by a nonnegative: `0 <= k` and `a <= b` ⇒ `a * k <= b * k`.
    MulRightNonnegativeMonotone(MulRightNonnegativeMonotoneBuiltinRuleProof),
    // Absolute-value upper bound from symmetric bounds: `x <= a` and `-x <= a` ⇒ `abs(x) <= a`.
    // Example: known `x <= 3` and `-x <= 3` prove `abs(x) <= 3`.
    AbsLeFromSymmetricBounds(AbsLeFromSymmetricBoundsBuiltinRuleProof),
    // Absolute-value upper bound implies the positive side: known `abs(x) <= a` ⇒ `x <= a`.
    AbsLeImpliesUpper(AbsLeImpliesUpperBuiltinRuleProof),
    // Absolute-value upper bound implies the negative side: known `abs(x) <= a` ⇒ `-x <= a`.
    AbsLeImpliesNegUpper(AbsLeImpliesNegUpperBuiltinRuleProof),
    // Self upper bound: `x <= abs(x)`.
    AbsSelfUpper(AbsSelfUpperBuiltinRuleProof),
    // Self lower bound: `-abs(x) <= x`.
    AbsSelfLower(AbsSelfLowerBuiltinRuleProof),
    // Triangle inequality: `abs(x + y) <= abs(x) + abs(y)`.
    AbsTriangleInequality(AbsTriangleInequalityBuiltinRuleProof),
    // Reverse triangle (add form): `abs(x) - abs(y) <= abs(x + y)`.
    // Example: prove `abs(a) - abs(b) <= abs(a + b)`.
    AbsReverseTriangleAdd(AbsReverseTriangleAddBuiltinRuleProof),
    // Reverse triangle (sub form): `abs(x) - abs(y) <= abs(x - y)`.
    // Example: prove `abs(a) - abs(b) <= abs(a - b)`.
    AbsReverseTriangleSub(AbsReverseTriangleSubBuiltinRuleProof),
    // Sum of nonnegatives is nonnegative: `0 <= a` and `0 <= b` ⇒ `0 <= a + b`.
    // Example: known `0 <= x`, `0 <= y` prove `0 <= x + y`.
    SumOfNonnegatives(SumOfNonnegativesBuiltinRuleProof),
    // Product of nonnegatives is nonnegative: `0 <= a` and `0 <= b` ⇒ `0 <= a * b`.
    // Example: known `0 <= x`, `0 <= y` prove `0 <= x * y`.
    ProductOfNonnegatives(ProductOfNonnegativesBuiltinRuleProof),
    // Even integer power is nonnegative: `0 <= a^(2k)` or `0 <= a * a`.
    // Mathematical property: for every real `a` and even integer `n`, `a^n >= 0`.
    // Example: prove `0 <= x^2`, `0 <= x * x`.
    EvenPowNonnegative(EvenPowNonnegativeBuiltinRuleProof),
    // Positive base power is nonnegative: `0 < a` ⇒ `0 <= a^b`.
    // Example: known `0 < a` proves `0 <= a^n`.
    PowNonnegFromPositiveBase(PowNonnegFromPositiveBaseBuiltinRuleProof),
    // Nonnegative base with positive-integer exponent: `0 <= a` and `n $in N+` ⇒ `0 <= a^n`.
    // Example: known `0 <= a`, `n $in N+` prove `0 <= a^n`.
    PowNonnegFromNonnegBasePosIntExp(PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof),
    // Square root is nonnegative: `0 <= x` ⇒ `0 <= sqrt(x)`.
    // Example: known `0 <= x` proves `0 <= sqrt(x)`.
    SqrtNonnegative(SqrtNonnegativeBuiltinRuleProof),
    // Square root is weakly monotone: `0 <= a`, `0 <= b`, `a <= b` ⇒ `sqrt(a) <= sqrt(b)`.
    // Example: known `0 <= a`, `0 <= b`, `a <= b` prove `sqrt(a) <= sqrt(b)`.
    SqrtMonotoneNondecreasing(SqrtMonotoneNondecreasingBuiltinRuleProof),
    // Positive-natural membership implies at least one: `n $in N+` ⇒ `1 <= n`.
    // Example: after `have n N+`, prove `1 <= n`.
    FromKnownInPositiveNatural(FromKnownInPositiveNaturalBuiltinRuleProof),
    // Log with base > 1 preserves weak order on positive args.
    // Mathematical property: `1 < a`, `0 < x`, `0 < y`, `x <= y` ⇒ `log(a, x) <= log(a, y)`.
    // Example: known `1 < 2`, `0 < x`, `0 < y`, `x <= y` prove `log(2, x) <= log(2, y)`.
    LogOrderPreservingWeak(LogOrderPreservingWeakBuiltinRuleProof),
    // Order transitivity: known `a <= b`/`a < b` and `b <= c`/`b < c` prove `a <= c`.
    // Example: known `x <= y` and `y <= z` prove `x <= z`.
    LessEqualTransitivity(LessEqualTransitivityBuiltinRuleProof),
    // Subtraction bridge: known `0 <= b - a` prove `a <= b`.
    // Example: known `0 <= y - x` proves `x <= y`.
    LessEqualFromNonnegDifference(LessEqualFromNonnegDifferenceBuiltinRuleProof),
    // Subtraction bridge: known `a <= b` prove `0 <= b - a`.
    // Example: known `x <= y` proves `0 <= y - x`.
    NonnegDifferenceFromLessEqual(NonnegDifferenceFromLessEqualBuiltinRuleProof),
    // Mod remainder nonnegative: `a $in Z`, `b $in N+` ⇒ `0 <= a % b`.
    // Example: after `have a Z` and `have b N+`, prove `0 <= a % b`.
    ModRemainderNonnegative(ModRemainderNonnegativeBuiltinRuleProof),
    // Positive common divisor preserves weak order.
    // Example: known `0 < c` and `a <= b` prove `a / c <= b / c`.
    DivMonotoneWeakSamePosDivisor(DivMonotoneWeakSamePosDivisorBuiltinRuleProof),
    // Finite-set cardinality is nonnegative.
    // Example: `$is_finite_set(S)` proves `0 <= finite_set_size(S)`.
    FiniteSetSizeNonnegativeLe(FiniteSetSizeNonnegativeLeBuiltinRuleProof),
    // Nonempty finite set has size at least one.
    // Example: `$is_finite_set(S)` and `$is_nonempty_set(S)` prove `1 <= finite_set_size(S)`.
    FiniteSetSizeAtLeastOneLe(FiniteSetSizeAtLeastOneLeBuiltinRuleProof),
    // Subset cannot raise finite cardinality.
    // Example: `A $subset B` with both finite proves `finite_set_size(A) <= finite_set_size(B)`.
    FiniteSetSizeSubsetLe(FiniteSetSizeSubsetLeBuiltinRuleProof),

    // Negative common divisor reverses weak order.
    // Mathematical property: `c < 0` and `b <= a` ⇒ `a / c <= b / c`.
    // Example: known `c < 0` and `y <= x` prove `x / c <= y / c`.
    DivMonotoneWeakSameNegDivisor(DivMonotoneWeakSameNegDivisorBuiltinRuleProof),
    // Move a positive factor into a right-hand quotient.
    // Mathematical property: `0 < c` and `c * a <= b` (or `a * c <= b`) ⇒ `a <= b / c`.
    // Example: known `0 < c` and `c * x <= y` prove `x <= y / c`.
    LessEqualFromPosDivProductBound(LessEqualFromPosDivProductBoundBuiltinRuleProof),
    // Move a positive denominator out of a left-hand quotient.
    // Mathematical property: `0 < c` and `a / c <= b` ⇒ `a <= b * c`.
    // Example: known `0 < c` and `x / c <= y` prove `x <= y * c`.
    LessEqualFromPosDenomQuotientBound(LessEqualFromPosDenomQuotientBoundBuiltinRuleProof),
    // Weaken a known numeric lower bound to a smaller literal weak goal.
    // Example: known `4 < x` proves `2 <= x`.
    NumericLowerBoundWeakenLe(NumericLowerBoundWeakenLeBuiltinRuleProof),
    // Integer discreteness from a strict predecessor lower bound.
    // Example: known `4 < x` and `x $in Z` prove `5 <= x`.
    NumericLowerBoundFromStrictPredecessorLe(NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof),
    // Weaken a known numeric upper bound to a larger literal weak goal.
    // Example: known `x < 4` proves `x <= 6`.
    NumericUpperBoundWeakenLe(NumericUpperBoundWeakenLeBuiltinRuleProof),
    // Integer successor: `a < b` ⇒ `a + 1 <= b`.
    // Example: known `m < n` for integers proves `m + 1 <= n`.
    IntegerSuccessorLe(IntegerSuccessorLeBuiltinRuleProof),
    // Integer adjacency: `a < b + 1` ⇒ `a <= b`.
    // Example: known `m < n + 1` for integers proves `m <= n`.
    IntegerAdjacencyLe(IntegerAdjacencyLeBuiltinRuleProof),
    // Integer predecessor: `a < b` ⇒ `a <= b - 1`.
    // Example: known `m < n` for integers proves `m <= n - 1`.
    IntegerPredecessorLe(IntegerPredecessorLeBuiltinRuleProof),
    // Integer difference: `a < b` ⇒ `1 <= b - a`.
    // Example: known `m < n` for integers proves `1 <= n - m`.
    IntegerDiffAtLeastOneLe(IntegerDiffAtLeastOneLeBuiltinRuleProof),
    // Members are at most the finite-set maximum.
    // Example: known `x $in S` proves `x <= finite_set_max(S)`.
    FiniteSetMaxMemberLe(FiniteSetMaxMemberLeBuiltinRuleProof),
    // The finite-set minimum is at most every member.
    // Example: known `x $in S` proves `finite_set_min(S) <= x`.
    FiniteSetMinMemberLe(FiniteSetMinMemberLeBuiltinRuleProof),
    // Union cardinality is at most the sum of the input cardinalities.
    // Example: `finite_set_size(union(A, B)) <= finite_set_size(A) + finite_set_size(B)`.
    FiniteSetSizeUnionLeSum(FiniteSetSizeUnionLeSumBuiltinRuleProof),
    // Surjection from a finite source bounds codomain size by source size.
    // Example: `$surjective(A, B, f)` and finite `A` prove `finite_set_size(B) <= finite_set_size(A)`.
    FiniteSetSizeSurjectionCodomainLeDomain(FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof),
    // Order flip: `(-1)*x <= 0` from known `x >= 0` or `x > 0`.
    // Example: trust a >= 0; (-1) * a <= 0.
    OrderFlipMulMinusOne(
        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessEqualBuiltinRuleProof,
    ),
    // Sign from a known negative literal upper bound: `x <= 0`.
    // Example: known `a <= -1` proves `a <= 0`.
    OrderSignFromNegativeLiteralBound(
        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromNegativeLiteralBoundBuiltinRuleProof,
    ),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct OrderReflexivityBuiltinRuleProof {
    pub repeated_object: Obj,
}

pub struct FromKnownLessBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct FromKnownInNaturalBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct ArcsinPrincipalLowerBoundBuiltinRuleProof {}
pub struct ArcsinPrincipalUpperBoundBuiltinRuleProof {}
pub struct ArccosPrincipalLowerBoundBuiltinRuleProof {}
pub struct ArccosPrincipalUpperBoundBuiltinRuleProof {}
pub struct UnitCircleLowerBoundBuiltinRuleProof {}
pub struct UnitCircleUpperBoundBuiltinRuleProof {}
pub struct AbsNonnegativeBuiltinRuleProof {}

pub struct AddRightNonnegativeBuiltinRuleProof {
    pub nonnegative_addend_proof: VerifyFactResult,
}

pub struct AddLeftNonnegativeBuiltinRuleProof {
    pub nonnegative_addend_proof: VerifyFactResult,
}

pub struct AddRightCongruenceBuiltinRuleProof {
    pub premise_proof: VerifyFactResult,
}

pub struct AddLeftCongruenceBuiltinRuleProof {
    pub premise_proof: VerifyFactResult,
}

pub struct SubNonnegativeBuiltinRuleProof {
    pub nonnegative_subtrahend_proof: VerifyFactResult,
}

pub struct MulLeftNonnegativeMonotoneBuiltinRuleProof {
    pub nonnegative_factor_proof: VerifyFactResult,
    pub order_premise_proof: VerifyFactResult,
}

pub struct MulRightNonnegativeMonotoneBuiltinRuleProof {
    pub nonnegative_factor_proof: VerifyFactResult,
    pub order_premise_proof: VerifyFactResult,
}

pub struct AbsLeFromSymmetricBoundsBuiltinRuleProof {
    pub upper_proof: VerifyFactResult,
    pub neg_upper_proof: VerifyFactResult,
}

pub struct AbsLeImpliesUpperBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct AbsLeImpliesNegUpperBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct AbsSelfUpperBuiltinRuleProof {}
pub struct AbsSelfLowerBuiltinRuleProof {}
pub struct AbsTriangleInequalityBuiltinRuleProof {}
pub struct AbsReverseTriangleAddBuiltinRuleProof {}
pub struct AbsReverseTriangleSubBuiltinRuleProof {}

pub struct SumOfNonnegativesBuiltinRuleProof {
    pub left_nonnegative_proof: VerifyFactResult,
    pub right_nonnegative_proof: VerifyFactResult,
}

pub struct ProductOfNonnegativesBuiltinRuleProof {
    pub left_nonnegative_proof: VerifyFactResult,
    pub right_nonnegative_proof: VerifyFactResult,
}

pub struct EvenPowNonnegativeBuiltinRuleProof {}

pub struct PowNonnegFromPositiveBaseBuiltinRuleProof {
    pub base_positive_proof: VerifyFactResult,
}

pub struct PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof {
    pub base_nonnegative_proof: VerifyFactResult,
    pub exp_in_positive_natural_proof: VerifyFactResult,
}

pub struct SqrtNonnegativeBuiltinRuleProof {
    pub arg_nonnegative_proof: VerifyFactResult,
}

pub struct SqrtMonotoneNondecreasingBuiltinRuleProof {
    pub left_nonnegative_proof: VerifyFactResult,
    pub right_nonnegative_proof: VerifyFactResult,
    pub args_order_proof: VerifyFactResult,
}

pub struct FromKnownInPositiveNaturalBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct LogOrderPreservingWeakBuiltinRuleProof {
    pub base_gt_one_proof: VerifyFactResult,
    pub left_arg_positive_proof: VerifyFactResult,
    pub right_arg_positive_proof: VerifyFactResult,
    pub args_order_proof: VerifyFactResult,
}

pub struct LessEqualTransitivityBuiltinRuleProof {
    pub left_to_mid_cite_fact_id: FactId,
    pub mid_to_right_cite_fact_id: FactId,
}

pub struct LessEqualFromNonnegDifferenceBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct NonnegDifferenceFromLessEqualBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct ModRemainderNonnegativeBuiltinRuleProof {
    pub dividend_in_z_proof: VerifyFactResult,
    pub modulus_in_n_pos_proof: VerifyFactResult,
}

pub struct DivMonotoneWeakSamePosDivisorBuiltinRuleProof {
    pub divisor_pos_proof: VerifyFactResult,
    pub numerators_order_proof: VerifyFactResult,
}

pub struct FiniteSetSizeNonnegativeLeBuiltinRuleProof {
    pub finite_proof: VerifyFactResult,
}

pub struct FiniteSetSizeAtLeastOneLeBuiltinRuleProof {
    pub finite_proof: VerifyFactResult,
    pub nonempty_proof: VerifyFactResult,
}

pub struct FiniteSetSizeSubsetLeBuiltinRuleProof {
    pub left_finite_proof: VerifyFactResult,
    pub right_finite_proof: VerifyFactResult,
    pub subset_proof: VerifyFactResult,
}




pub struct DivMonotoneWeakSameNegDivisorBuiltinRuleProof {
    pub divisor_neg_proof: VerifyFactResult,
    pub numerators_order_proof: VerifyFactResult,
}

pub struct LessEqualFromPosDivProductBoundBuiltinRuleProof {
    pub divisor_pos_proof: VerifyFactResult,
    pub product_bound_proof: VerifyFactResult,
}

pub struct LessEqualFromPosDenomQuotientBoundBuiltinRuleProof {
    pub divisor_pos_proof: VerifyFactResult,
    pub quotient_bound_proof: VerifyFactResult,
}

pub struct NumericLowerBoundWeakenLeBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof {
    pub cite_fact_id: FactId,
    pub in_z_proof: VerifyFactResult,
}

pub struct NumericUpperBoundWeakenLeBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct IntegerSuccessorLeBuiltinRuleProof {
    pub left_in_z_proof: VerifyFactResult,
    pub right_in_z_proof: VerifyFactResult,
    pub strict_proof: VerifyFactResult,
}

pub struct IntegerAdjacencyLeBuiltinRuleProof {
    pub left_in_z_proof: VerifyFactResult,
    pub right_in_z_proof: VerifyFactResult,
    pub strict_proof: VerifyFactResult,
}

pub struct IntegerPredecessorLeBuiltinRuleProof {
    pub left_in_z_proof: VerifyFactResult,
    pub right_in_z_proof: VerifyFactResult,
    pub strict_proof: VerifyFactResult,
}

pub struct IntegerDiffAtLeastOneLeBuiltinRuleProof {
    pub left_in_z_proof: VerifyFactResult,
    pub right_in_z_proof: VerifyFactResult,
    pub strict_proof: VerifyFactResult,
}

pub struct FiniteSetMaxMemberLeBuiltinRuleProof {
    pub member_proof: VerifyFactResult,
}

pub struct FiniteSetMinMemberLeBuiltinRuleProof {
    pub member_proof: VerifyFactResult,
}

pub struct FiniteSetSizeUnionLeSumBuiltinRuleProof {
    pub left_finite_proof: VerifyFactResult,
    pub right_finite_proof: VerifyFactResult,
}

pub struct FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof {
    pub cite_surjection_fact_id: FactId,
    pub domain_finite_proof: VerifyFactResult,
}


impl Runtime {
    // Builtin search for `a <= b`.
    // B0: reflexivity + known cites (shape-independent).
    // A: Obj-shape match (arithmetic / abs / trig).
    // B1: closed decimal evaluation.
    // Example: prove `a <= a`, `x <= x + 1`, `abs(x+y) <= abs(x)+abs(y)`, `1 <= 2`.
    pub fn search_less_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        // B0 — non-shape
        if fact.left.ir() == fact.right.ir() {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::OrderReflexivity(
                    OrderReflexivityBuiltinRuleProof {
                        repeated_object: fact.left.clone(),
                    },
                ),
            ));
        }
        if let Some(cite_fact_id) = self.known_less_fact_id(&fact.left, &fact.right) {
            return Ok(Some(LessEqualFactSearchProofByBuiltinRule::FromKnownLess(
                FromKnownLessBuiltinRuleProof { cite_fact_id },
            )));
        }
        if let Some(proof) = self.try_order_flip_mul_minus_one_to_less_equal(fact) {
            return Ok(Some(LessEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(
                proof,
            )));
        }
        if let Some(proof) = self.try_order_sign_from_negative_literal_bound(fact) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::OrderSignFromNegativeLiteralBound(proof),
            ));
        }
        if let Some(proof) = self.abs_le_implies_upper_proof(fact) {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.abs_le_implies_neg_upper_proof(fact) {
            return Ok(Some(proof));
        }

        // A — shape match on (left, right) Obj constructors
        if let Some(proof) =
            self.search_order_abs_algebra_less_equal_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_order_power_sqrt_log_less_equal_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_order_div_mod_bridge_trans_less_equal_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_order_stage_a_remainder_less_equal_proof(fact, verify_state)?
        {
            return Ok(Some(proof));
        }

        // B1 — closed numeric
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if matches!(cmp, NumberCompareResult::Greater) {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }
}

pub(super) fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}

pub(super) fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "0"
    )
}
