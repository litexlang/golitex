use super::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation;
use crate::ast::fact::EqualFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    algebraic_normalization_nonzero_requirements, evaluate_obj_to_normalized_decimal_number,
    objs_equal_by_rational_expression_evaluation, objs_equal_by_complex_expression_evaluation, contains_imaginary_unit,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin Calculation search for EqualFact.
    // Mathematical property: see EqualitySearchProofByCalculation.
    // Simple: `1 + 1 = 2`; Rational: `(x + 1) * (x - 1) = x^2 - 1`.
    // Complex closed nested trees (ClosedDecimal path):
    //   examples/.../calculation_closed_decimal_complex_nested.lit
    //   e.g. `sqrt(4) * log(2, 8) + floor(2.5)! = 8`.
    // Symbolic nonzero premises belong to the guarded rational strategy.
    pub fn search_equal_fact_by_calculation(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByCalculation>> {
        if let (Some(left), Some(right)) = (
            evaluate_obj_to_normalized_decimal_number(&fact.left),
            evaluate_obj_to_normalized_decimal_number(&fact.right),
        ) {
            if left.normalized_value == right.normalized_value {
                return Ok(Some(EqualitySearchProofByCalculation::ClosedDecimal {
                    left_normal: left.normalized_value,
                    right_normal: right.normalized_value,
                }));
            }
        }

        if objs_equal_by_rational_expression_evaluation(&fact.left, &fact.right)
            && algebraic_normalization_nonzero_requirements(&fact.left, &fact.right).is_empty()
        {
            return Ok(Some(EqualitySearchProofByCalculation::Rational {}));
        }

        // Closed numeric nonzero denominators are calculation leaves. Symbolic
        // denominators remain owned by the strategy with explicit premises.
        let complex_requirements_are_closed_nonzero =
            algebraic_normalization_nonzero_requirements(&fact.left, &fact.right)
                .iter().all(|obj| evaluate_obj_to_normalized_decimal_number(obj)
                    .is_some_and(|number| number.normalized_value != "0"));
        if (contains_imaginary_unit(&fact.left) || contains_imaginary_unit(&fact.right))
            && complex_requirements_are_closed_nonzero
            && objs_equal_by_complex_expression_evaluation(&fact.left, &fact.right)
        {
            return Ok(Some(EqualitySearchProofByCalculation::Complex {}));
        }

        Ok(None)
    }
}
