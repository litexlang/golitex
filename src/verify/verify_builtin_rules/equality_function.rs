use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::factual_equal_success_by_builtin_reason;

impl Runtime {
    /// The positive-power recursion for square real matrices.
    /// Example: `A '^ 1 = A` and `A '^ (k + 1) = (A '^ k) '* A`.
    pub(crate) fn try_verify_matrix_power_definition(
        &self,
        statement_left: &Obj,
        statement_right: &Obj,
        power_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        let Obj::MatrixPow(power) = power_side else {
            return None;
        };
        let one: Obj = Number::new("1".to_string()).into();
        if !self
            .verify_objs_are_equal_by_known_equality(&power.exponent, &one, line_file.clone())
            .is_unknown()
            && !self
                .verify_objs_are_equal_by_known_equality(&power.base, other_side, line_file.clone())
                .is_unknown()
        {
            return Some(factual_equal_success_by_builtin_reason(
                statement_left,
                statement_right,
                line_file,
                "matrix positive power base case: A '^ 1 = A",
            ));
        }

        let Obj::Add(exponent) = power.exponent.as_ref() else {
            return None;
        };
        let predecessor = if !self
            .verify_objs_are_equal_by_known_equality(&exponent.right, &one, line_file.clone())
            .is_unknown()
        {
            exponent.left.as_ref()
        } else if !self
            .verify_objs_are_equal_by_known_equality(&exponent.left, &one, line_file.clone())
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
            self.verify_objs_are_equal_by_known_equality(left, right, line_file.clone())
                .is_unknown()
        }) {
            return None;
        }
        Some(factual_equal_success_by_builtin_reason(
            statement_left,
            statement_right,
            line_file,
            "matrix positive power recursion: A '^(k + 1) = (A '^ k) '* A",
        ))
    }
}
