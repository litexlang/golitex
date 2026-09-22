use crate::new_pipeline::ast::fact::LessEqualFact;
use crate::new_pipeline::ast::obj::{Number, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::trig_bounds::{
    match_arccos_principal_lower, match_arccos_principal_upper, match_arcsin_principal_lower,
    match_arcsin_principal_upper, match_unit_circle_lower, match_unit_circle_upper,
};
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

impl Runtime {
    // Builtin: reflexivity, known `<`, trig principal/unit bounds, then closed decimal `<=`.
    pub fn search_less_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
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
        if is_zero_obj(&fact.left) {
            if let Some(cite_fact_id) = self.known_in_natural_fact_id(&fact.right) {
                return Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::FromKnownInNatural(
                        FromKnownInNaturalBuiltinRuleProof { cite_fact_id },
                    ),
                ));
            }
        }
        if match_arcsin_principal_lower(&fact.left, &fact.right) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::ArcsinPrincipalLowerBound(
                    ArcsinPrincipalLowerBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_arcsin_principal_upper(&fact.left, &fact.right) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::ArcsinPrincipalUpperBound(
                    ArcsinPrincipalUpperBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_arccos_principal_lower(&fact.left, &fact.right) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::ArccosPrincipalLowerBound(
                    ArccosPrincipalLowerBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_arccos_principal_upper(&fact.left, &fact.right) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::ArccosPrincipalUpperBound(
                    ArccosPrincipalUpperBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_unit_circle_lower(&fact.left, &fact.right) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::UnitCircleLowerBound(
                    UnitCircleLowerBoundBuiltinRuleProof {},
                ),
            ));
        }
        if match_unit_circle_upper(&fact.left, &fact.right) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::UnitCircleUpperBound(
                    UnitCircleUpperBoundBuiltinRuleProof {},
                ),
            ));
        }
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

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Number(Number {
            normalized_value,
        }) if normalized_value == "0"
    )
}
