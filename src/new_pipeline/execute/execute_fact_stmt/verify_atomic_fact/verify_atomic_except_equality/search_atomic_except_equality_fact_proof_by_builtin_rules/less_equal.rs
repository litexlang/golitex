use crate::new_pipeline::ast::fact::LessEqualFact;
use crate::new_pipeline::ast::obj::{Number, Obj};
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

impl Runtime {
    // Builtin: reflexivity, known `<`, then closed decimal `<=`.
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
