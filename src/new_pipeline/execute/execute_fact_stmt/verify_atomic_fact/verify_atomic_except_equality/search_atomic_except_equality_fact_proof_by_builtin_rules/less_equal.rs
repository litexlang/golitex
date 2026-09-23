use crate::new_pipeline::ast::fact::LessEqualFact;
use crate::new_pipeline::ast::obj::{Literal, Number, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

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
        if let Some(proof) = self.abs_le_implies_upper_proof(fact) {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.abs_le_implies_neg_upper_proof(fact) {
            return Ok(Some(proof));
        }

        // A — shape match on (left, right) Obj constructors
        if let Some(proof) =
            self.search_order_abs_algebra_less_equal_proof(fact, verify_state)?
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
