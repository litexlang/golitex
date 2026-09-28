use super::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::{
    algebraic_normalization_nonzero_requirements, evaluate_obj_to_normalized_decimal_number,
    objs_equal_by_rational_expression_evaluation,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin Calculation search for EqualFact.
    // Mathematical property: see EqualitySearchProofByCalculation.
    // Simple: `1 + 1 = 2`; Rational: `(x + 1) * (x - 1) = x^2 - 1`.
    // Complex closed nested trees (ClosedDecimal path):
    //   examples/.../calculation_closed_decimal_complex_nested.lit
    //   e.g. `sqrt(4) * log(2, 8) + floor(2.5)! = 8`.
    // Identities that need nonzero premises are not accepted here.
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

        Ok(None)
    }
}
