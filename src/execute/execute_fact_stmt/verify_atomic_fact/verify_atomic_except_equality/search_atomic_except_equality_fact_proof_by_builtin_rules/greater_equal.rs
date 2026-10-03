use super::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::GreaterEqualFact;
use crate::ast::obj::{ArithmeticOperator, Literal, Number, Obj, Sub};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::predecessor_helpers::is_number_value;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_numeric_objs, NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::execute::execute_fact_stmt::VerifyFactResult;

// Builtin rules for `a >= b`.
pub enum GreaterEqualFactSearchProofByBuiltinRule {
    ComplexModulusNonnegative,
    // Converse order, citing an existing opposite-direction comparison.
    FromKnownLessEqual(FromKnownLessEqualBuiltinRuleProof),
    FromKnownOrderComplement(FromKnownOrderComplementBuiltinRuleProof),
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
    // Positive-natural membership implies at least one: `n $in N+` ⇒ `n >= 1`.
    // Example: after `have n N+`, prove `n >= 1`.
    FromKnownInPositiveNatural(FromKnownInPositiveNaturalBuiltinRuleProof),
    // Predecessor stays non-negative from a known lower bound of one.
    // Mathematical property: `x >= 1` ⇒ `x - 1 >= 0`.
    // Example: known `n >= 1` proves `n - 1 >= 0`.
    PredecessorNonNegFromAtLeastOne(PredecessorNonNegFromAtLeastOneBuiltinRuleProof),
    // Finite-set cardinality is nonnegative.
    // Example: `$is_finite_set(S)` proves `finite_set_size(S) >= 0`.
    FiniteSetSizeNonnegative(FiniteSetSizeNonnegativeBuiltinRuleProof),
    // Nonempty finite set has size at least one.
    // Example: `$is_finite_set(S)` and `$is_nonempty_set(S)` prove `finite_set_size(S) >= 1`.
    FiniteSetSizeAtLeastOne(FiniteSetSizeAtLeastOneBuiltinRuleProof),
    // Order flip: `(-1)*x >= 0` from known `x < 0` or `x <= 0`.
    // Example: trust a < 0; (-1) * a >= 0.
    OrderFlipMulMinusOne(
        crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof,
    ),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct OrderReflexivityBuiltinRuleProof {
    pub repeated_object: Obj,
}

pub struct FromKnownGreaterBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

pub struct FromKnownInPositiveNaturalBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

pub struct PredecessorNonNegFromAtLeastOneBuiltinRuleProof {
    pub at_least_one_proof: AtomicExceptEqualityFactKnownProof,
}

pub struct FiniteSetSizeNonnegativeBuiltinRuleProof {
    pub finite_proof: VerifyFactResult,
}

pub struct FiniteSetSizeAtLeastOneBuiltinRuleProof {
    pub finite_proof: VerifyFactResult,
    pub nonempty_proof: VerifyFactResult,
}


pub struct FromKnownLessEqualBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

impl Runtime {
    // Builtin search for `a >= b`.
    // B0: reflexivity + known `>`. A: match Obj shapes. B1: closed decimal.
    // Example: prove `a >= a`, `n >= 0`, `n - 1 >= 0`, `2 >= 1`.
    pub fn search_greater_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &GreaterEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        // Principal complex modulus is nonnegative after argument/output WD.
        // Example: have z C; C_abs(z) >= 0.
        if matches!(&fact.left, Obj::ComplexOperator(crate::ast::obj::ComplexOperator::ComplexAbs(_)))
            && is_number_value(&fact.right, "0") {
            return Ok(Some(GreaterEqualFactSearchProofByBuiltinRule::ComplexModulusNonnegative));
        }
        if let Some(premise_proof) = self.known_less_equal_proof(&fact.right, &fact.left) {
            return Ok(Some(GreaterEqualFactSearchProofByBuiltinRule::FromKnownLessEqual(FromKnownLessEqualBuiltinRuleProof { premise_proof })));
        }
        if let Some(proof) = self.known_order_complement(fact.clone().into(), verify_state.clone())? {
            return Ok(Some(GreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof)));
        }
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
        if let Some(premise_proof) = self.known_greater_proof(&fact.left, &fact.right) {
            return Ok(Some(
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownGreater(
                    FromKnownGreaterBuiltinRuleProof { premise_proof },
                ),
            ));
        }
        if let Some(proof) = self.try_order_flip_mul_minus_one_to_greater_equal(fact) {
            return Ok(Some(
                GreaterEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(proof),
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
                if let Some(at_least_one_proof) =
                    self.known_greater_equal_proof(left.as_ref(), &one)
                {
                    return Ok(Some(
                        GreaterEqualFactSearchProofByBuiltinRule::PredecessorNonNegFromAtLeastOne(
                            PredecessorNonNegFromAtLeastOneBuiltinRuleProof {
                                at_least_one_proof,
                            },
                        ),
                    ));
                }
            }
            (left, right) if is_one_obj(right) => {
                if let Some(premise_proof) = self.search_in_positive_natural_premise(left, verify_state)? {
                    return Ok(Some(
                        GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(
                            FromKnownInPositiveNaturalBuiltinRuleProof { premise_proof },
                        ),
                    ));
                }
            }
            _ => {}
        }

        if let Some(proof) = self.search_order_finite_set_size_greater_equal_proof(
            &fact.left,
            &fact.right,
            verify_state,
        )? {
            return Ok(Some(proof));
        }

        // B1 — closed numeric
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_numeric_objs(&fact.left, &fact.right)
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


}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "1"
    )
}
