use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::factual_equal_success_by_builtin_reason;

impl Runtime {
    /// The positive-power recursion for square real matrices.
    /// Example: `A '^ 1 = A` and `A '^ (k + 1) = (A '^ k) '* A`.
    pub(crate) fn try_verify_matrix_power_definition(
        &self,
        equal_fact: &EqualFact,
    ) -> Option<StmtResult> {
        self.try_verify_matrix_power_definition_in_direction(equal_fact, true)
            .or_else(|| self.try_verify_matrix_power_definition_in_direction(equal_fact, false))
    }

    fn try_verify_matrix_power_definition_in_direction(
        &self,
        equal_fact: &EqualFact,
        power_is_left: bool,
    ) -> Option<StmtResult> {
        let (power_side, other_side) = if power_is_left {
            (&equal_fact.left, &equal_fact.right)
        } else {
            (&equal_fact.right, &equal_fact.left)
        };
        let line_file = equal_fact.line_file.clone();
        let Obj::MatrixPow(power) = power_side else {
            return None;
        };
        let one: Obj = Number::new("1".to_string()).into();
        if !self
            .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                &power.exponent,
                &one,
                line_file.clone(),
            ))
            .is_unknown()
            && !self
                .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                    &power.base,
                    other_side,
                    line_file.clone(),
                ))
                .is_unknown()
        {
            return Some(factual_equal_success_by_builtin_reason(
                equal_fact,
                "matrix positive power base case: A '^ 1 = A",
            ));
        }

        let Obj::Add(exponent) = power.exponent.as_ref() else {
            return None;
        };
        let predecessor = if !self
            .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                &exponent.right,
                &one,
                line_file.clone(),
            ))
            .is_unknown()
        {
            exponent.left.as_ref()
        } else if !self
            .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                &exponent.left,
                &one,
                line_file.clone(),
            ))
            .is_unknown()
        {
            exponent.right.as_ref()
        } else {
            return None;
        };
        let Obj::MatrixMul(product) = other_side else {
            return None;
        };
        let Obj::MatrixPow(previous_power) = product.left.as_ref() else {
            return None;
        };
        let pairs = [
            (power.base.as_ref(), previous_power.base.as_ref()),
            (power.base.as_ref(), product.right.as_ref()),
            (predecessor, previous_power.exponent.as_ref()),
        ];
        if pairs.iter().any(|(left, right)| {
            self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                left,
                right,
                line_file.clone(),
            ))
            .is_unknown()
        }) {
            return None;
        }
        Some(factual_equal_success_by_builtin_reason(
            equal_fact,
            "matrix positive power recursion: A '^(k + 1) = (A '^ k) '* A",
        ))
    }
}
