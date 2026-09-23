use crate::new_pipeline::ast::fact::GreaterEqualFact;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Literal, Number, Obj, StandardSet, Sub};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::is_number_value;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::keywords::IN;
use crate::new_pipeline::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rules for `a >= b`.
pub enum GreaterEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L >= R,
    // then `left >= right`.
    // Examples: `2 >= 1`, `2 >= 2`, `3 >= 1 + 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Order reflexivity: `x >= x`.
    // Mathematical property: >= is reflexive on any object.
    // Example: prove `a >= a`.
    OrderReflexivity(OrderReflexivityBuiltinRuleProof),
    // Strict order implies weak order.
    // Mathematical property: `a > b` ⇒ `a >= b`.
    // Example: known `x > 0` proves `x >= 0`.
    FromKnownGreater(FromKnownGreaterBuiltinRuleProof),
    // Natural membership implies non-negative.
    // Mathematical property: `n $in N` ⇒ `n >= 0`.
    // Example: after `have n N`, prove `n >= 0`.
    FromKnownInNatural(FromKnownInNaturalBuiltinRuleProof),
    // Predecessor stays non-negative from a known lower bound of one.
    // Mathematical property: `x >= 1` ⇒ `x - 1 >= 0`.
    // Example: known `n >= 1` proves `n - 1 >= 0`.
    PredecessorNonNegFromAtLeastOne(PredecessorNonNegFromAtLeastOneBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct OrderReflexivityBuiltinRuleProof {
    pub repeated_object: Obj,
}

pub struct FromKnownGreaterBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct FromKnownInNaturalBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

pub struct PredecessorNonNegFromAtLeastOneBuiltinRuleProof {
    pub cite_at_least_one_fact_id: FactId,
}

impl Runtime {
    // Builtin search for `a >= b`.
    // B0: reflexivity + known `>`. A: match Obj shapes. B1: closed decimal.
    // Example: prove `a >= a`, `n >= 0`, `n - 1 >= 0`, `2 >= 1`.
    pub fn search_greater_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &GreaterEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        // B0 — non-shape
        if fact.left.ir() == fact.right.ir() {
            return Ok(Some(
                GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(
                    OrderReflexivityBuiltinRuleProof {
                        repeated_object: fact.left.clone(),
                    },
                ),
            ));
        }
        if let Some(cite_fact_id) = self.known_greater_fact_id(&fact.left, &fact.right) {
            return Ok(Some(
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownGreater(
                    FromKnownGreaterBuiltinRuleProof { cite_fact_id },
                ),
            ));
        }

        // A — shape: goals ending at 0
        match (&fact.left, &fact.right) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })),
                zero,
            ) if is_number_value(right.as_ref(), "1") && is_number_value(zero, "0") => {
                let one = Obj::Literal(Literal::Number(Number {
                    normalized_value: "1".to_string(),
                }));
                if let Some(cite_at_least_one_fact_id) =
                    self.known_greater_equal_fact_id(left.as_ref(), &one)
                {
                    return Ok(Some(
                        GreaterEqualFactSearchProofByBuiltinRule::PredecessorNonNegFromAtLeastOne(
                            PredecessorNonNegFromAtLeastOneBuiltinRuleProof {
                                cite_at_least_one_fact_id,
                            },
                        ),
                    ));
                }
            }
            (left, zero) if is_number_value(zero, "0") => {
                if let Some(cite_fact_id) = self.known_in_natural_fact_id(left) {
                    return Ok(Some(
                        GreaterEqualFactSearchProofByBuiltinRule::FromKnownInNatural(
                            FromKnownInNaturalBuiltinRuleProof { cite_fact_id },
                        ),
                    ));
                }
            }
            _ => {}
        }

        // B1 — closed numeric
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if matches!(cmp, NumberCompareResult::Less) {
            return Ok(None);
        }
        Ok(Some(
            GreaterEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }

    pub(crate) fn known_in_natural_fact_id(&self, element: &Obj) -> Option<FactId> {
        let key = (AtomicName::Plain { name: IN.into() }, true);
        let element_ir = element.ir();
        let n_ir = Obj::StandardSet(StandardSet::N).ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let crate::new_pipeline::ast::fact::AtomicFact::InFact(f) = known {
                    if f.element.ir() == element_ir && f.set.ir() == n_ir {
                        return Some(f.fact_id);
                    }
                }
            }
        }
        None
    }
}
