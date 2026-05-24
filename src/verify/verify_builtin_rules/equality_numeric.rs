use crate::prelude::*;
use crate::verify::verify_builtin_rules::{
    compare_normalized_number_str_to_zero, normalized_decimal_string_is_even_integer,
    NumberCompareResult,
};
use crate::verify::verify_equality_by_builtin_rules::*;
use crate::verify::verify_number_in_standard_set::is_integer_after_simplification;

impl Runtime {
    fn literal_one_obj_for_log_builtin() -> Obj {
        Obj::Number(Number::new("1".to_string()))
    }

    fn literal_neg_one_obj_for_log_builtin() -> Obj {
        Obj::Number(Number::new("-1".to_string()))
    }

    fn literal_zero_obj_for_abs_builtin() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    fn obj_is_literal_neg_one_for_abs_builtin(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "-1",
            _ => false,
        }
    }

    fn obj_is_negation_of_for_abs_builtin(obj: &Obj, expected_arg: &Obj) -> bool {
        match obj {
            Obj::Mul(m) => {
                (Self::obj_is_literal_neg_one_for_abs_builtin(m.left.as_ref())
                    && objs_equal_by_display_string(m.right.as_ref(), expected_arg))
                    || (Self::obj_is_literal_neg_one_for_abs_builtin(m.right.as_ref())
                        && objs_equal_by_display_string(m.left.as_ref(), expected_arg))
            }
            _ => false,
        }
    }

    fn obj_is_abs_product_for_abs_builtin(obj: &Obj, x: &Obj, y: &Obj) -> bool {
        let Obj::Mul(m) = obj else {
            return false;
        };
        match (m.left.as_ref(), m.right.as_ref()) {
            (Obj::Abs(left_abs), Obj::Abs(right_abs)) => {
                objs_equal_by_display_string(left_abs.arg.as_ref(), x)
                    && objs_equal_by_display_string(right_abs.arg.as_ref(), y)
            }
            _ => false,
        }
    }

    fn try_verify_abs_nonnegative_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (arg, other) = match (left, right) {
            (Obj::Abs(abs), other) => (abs.arg.as_ref(), other),
            (other, Obj::Abs(abs)) => (abs.arg.as_ref(), other),
            _ => return Ok(None),
        };
        if !objs_equal_by_display_string(arg, other) {
            return Ok(None);
        }
        let nonnegative: AtomicFact = LessEqualFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            arg.clone(),
            line_file.clone(),
        )
        .into();
        let nonnegative_result =
            self.verify_non_equational_known_then_builtin_rules_only(&nonnegative, verify_state)?;
        if !nonnegative_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "abs: abs(x) = x from 0 <= x".to_string(),
                vec![nonnegative_result],
            )
            .into(),
        ))
    }

    fn try_verify_abs_nonpositive_negation(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (arg, other) = match (left, right) {
            (Obj::Abs(abs), other) => (abs.arg.as_ref(), other),
            (other, Obj::Abs(abs)) => (abs.arg.as_ref(), other),
            _ => return Ok(None),
        };
        if !Self::obj_is_negation_of_for_abs_builtin(other, arg) {
            return Ok(None);
        }
        let nonpositive: AtomicFact = LessEqualFact::new(
            arg.clone(),
            Self::literal_zero_obj_for_abs_builtin(),
            line_file.clone(),
        )
        .into();
        let nonpositive_result =
            self.verify_non_equational_known_then_builtin_rules_only(&nonpositive, verify_state)?;
        if !nonpositive_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "abs: abs(x) = -x from x <= 0".to_string(),
                vec![nonpositive_result],
            )
            .into(),
        ))
    }

    fn try_verify_abs_product(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let matches_abs_product = |abs_side: &Obj, product_side: &Obj| -> bool {
            let Obj::Abs(abs) = abs_side else {
                return false;
            };
            let Obj::Mul(inner_mul) = abs.arg.as_ref() else {
                return false;
            };
            Self::obj_is_abs_product_for_abs_builtin(
                product_side,
                inner_mul.left.as_ref(),
                inner_mul.right.as_ref(),
            )
        };

        if !matches_abs_product(left, right) && !matches_abs_product(right, left) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "abs: abs(x * y) = abs(x) * abs(y)",
        )))
    }

    // Even powers ignore sign, so `x^2 = abs(x)^2`.
    // Example: `forall x R: x ^ 4 = abs(x) ^ 4`.
    fn try_verify_abs_even_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Pow(left_pow), Obj::Pow(right_pow)) = (left, right) else {
            return Ok(None);
        };
        if !objs_equal_by_display_string(left_pow.exponent.as_ref(), right_pow.exponent.as_ref()) {
            return Ok(None);
        }
        let Obj::Number(exp_num) = left_pow.exponent.as_ref() else {
            return Ok(None);
        };
        if !normalized_decimal_string_is_even_integer(&exp_num.normalized_value) {
            return Ok(None);
        }

        let bases_match = match (left_pow.base.as_ref(), right_pow.base.as_ref()) {
            (Obj::Abs(abs), other) => objs_equal_by_display_string(abs.arg.as_ref(), other),
            (other, Obj::Abs(abs)) => objs_equal_by_display_string(other, abs.arg.as_ref()),
            _ => false,
        };
        if !bases_match {
            return Ok(None);
        }

        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "abs: x^n = abs(x)^n for even integer n",
        )))
    }

    fn try_verify_zero_from_abs_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let zero = Self::literal_zero_obj_for_abs_builtin();
        let arg = if objs_equal_by_display_string(left, &zero) {
            right
        } else if objs_equal_by_display_string(right, &zero) {
            left
        } else {
            return Ok(None);
        };
        let abs_arg: Obj = Abs::new(arg.clone()).into();
        if !self.objs_have_same_known_equality_rc_in_some_env(&abs_arg, &zero) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "abs: x = 0 from abs(x) = 0",
        )))
    }

    pub(crate) fn try_verify_abs_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_abs_nonnegative_identity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_abs_nonpositive_negation(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_abs_product(left, right, line_file.clone())? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_abs_even_power(left, right, line_file.clone())? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_zero_from_abs_zero(left, right, line_file)? {
            return Ok(Some(done));
        }
        Ok(None)
    }

    fn obj_is_builtin_literal_zero(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => matches!(
                compare_normalized_number_str_to_zero(&n.normalized_value),
                NumberCompareResult::Equal
            ),
            _ => false,
        }
    }

    fn obj_is_builtin_literal_one(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "1",
            _ => false,
        }
    }

    // Literal 0 vs `x - y`: verify the equality if `x = y` holds via the full equality pipeline.
    pub(crate) fn try_verify_zero_equals_subtraction_implies_equal_operands(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (x, y) = if Self::obj_is_builtin_literal_zero(left) {
            match right {
                Obj::Sub(s) => (s.left.as_ref(), s.right.as_ref()),
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_zero(right) {
            match left {
                Obj::Sub(s) => (s.left.as_ref(), s.right.as_ref()),
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };

        let inner =
            self.verify_objs_are_equal_in_equality_builtin(x, y, line_file.clone(), verify_state)?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: 0 = x - y with x = y (known or builtin)",
            )));
        }
        Ok(None)
    }

    // Zero-product cancellation: from `a * b = 0` and `a != 0`, infer `b = 0` (and symmetrically).
    // Example: from `(x - 1) * y = 0` and `x - 1 != 0`, prove `y = 0`.
    fn verify_zero_product_factor_matches_target(
        &mut self,
        target: &Obj,
        factor: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Do not call the full equality builtin here; that would re-enter zero-product
        // cancellation while this rule is already trying to match a factor.
        let known_result = self.verify_objs_are_equal_known_only(target, factor, line_file.clone());
        if known_result.is_true() {
            return Ok(known_result);
        }

        let (calculation_result, _, _) = self
            .verify_equality_by_they_are_the_same_and_calculation(
                target,
                factor,
                line_file.clone(),
                verify_state,
            )?;
        if calculation_result.is_true() {
            return Ok(calculation_result);
        }

        if let Some(shape_result) =
            self.try_verify_equal_by_same_shape_and_known_equality_args(target, factor, line_file)
        {
            if shape_result.is_true() {
                return Ok(shape_result);
            }
        }

        Ok(StmtResult::StmtUnknown(StmtUnknown::new()))
    }

    pub(crate) fn try_verify_zero_equals_product_implies_other_factor_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let target = if Self::obj_is_builtin_literal_zero(left) {
            right
        } else if Self::obj_is_builtin_literal_zero(right) {
            left
        } else {
            return Ok(None);
        };

        let zero_obj = Self::literal_zero_obj_for_abs_builtin();
        let zero_key = zero_obj.to_string();
        let zero_equal_objs_by_env: Vec<Vec<Obj>> = self
            .iter_environments_from_top()
            .filter_map(|env| {
                env.known_equality
                    .get(&zero_key)
                    .map(|(_, equal_objs)| equal_objs.iter().cloned().collect())
            })
            .collect();

        for zero_equal_objs in zero_equal_objs_by_env {
            for equal_obj in zero_equal_objs {
                let Obj::Mul(mul) = equal_obj else {
                    continue;
                };

                let left_target_result = self.verify_zero_product_factor_matches_target(
                    target,
                    mul.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if left_target_result.is_true() {
                    let right_nonzero: AtomicFact = NotEqualFact::new(
                        mul.right.as_ref().clone(),
                        zero_obj.clone(),
                        line_file.clone(),
                    )
                    .into();
                    let right_nonzero_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &right_nonzero,
                            verify_state,
                        )?;
                    if right_nonzero_result.is_true() {
                        return Ok(Some(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                                "equality: b = 0 from a * b = 0 and a != 0".to_string(),
                                vec![left_target_result, right_nonzero_result],
                            )
                            .into(),
                        ));
                    }
                }

                let right_target_result = self.verify_zero_product_factor_matches_target(
                    target,
                    mul.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if right_target_result.is_true() {
                    let left_nonzero: AtomicFact = NotEqualFact::new(
                        mul.left.as_ref().clone(),
                        zero_obj.clone(),
                        line_file.clone(),
                    )
                    .into();
                    let left_nonzero_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &left_nonzero,
                            verify_state,
                        )?;
                    if left_nonzero_result.is_true() {
                        return Ok(Some(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                                "equality: a = 0 from a * b = 0 and b != 0".to_string(),
                                vec![right_target_result, left_nonzero_result],
                            )
                            .into(),
                        ));
                    }
                }
            }
        }

        Ok(None)
    }

    // 0 = a^n when n is a literal integer > 0 (avoids 0^0 /0^negative), from a = 0.
    pub(crate) fn try_verify_zero_equals_pow_from_base_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let pow = if Self::obj_is_builtin_literal_zero(left) {
            match right {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_zero(right) {
            match left {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        let Obj::Number(exp_num) = pow.exponent.as_ref() else {
            return Ok(None);
        };
        if !is_integer_after_simplification(exp_num) {
            return Ok(None);
        }
        if !matches!(
            compare_normalized_number_str_to_zero(&exp_num.normalized_value),
            NumberCompareResult::Greater
        ) {
            return Ok(None);
        }

        let base = pow.base.as_ref();
        let zero_side = if Self::obj_is_builtin_literal_zero(left) {
            left
        } else {
            right
        };
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            base,
            zero_side,
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: 0 = a^n from a = 0, n positive integer literal",
            )));
        }
        Ok(None)
    }

    // Zero is divisible by every non-zero integer modulus: `0 % m = 0`.
    // Example: `forall m Z: m != 0 =>: 0 % m = 0`.
    pub(crate) fn try_verify_zero_mod_equals_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let mod_obj = if Self::obj_is_builtin_literal_zero(left) {
            match right {
                Obj::Mod(m) => m,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_zero(right) {
            match left {
                Obj::Mod(m) => m,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_zero(mod_obj.left.as_ref()) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: 0 % m = 0",
        )))
    }

    // Every integer is congruent to zero modulo one: `x % 1 = 0`.
    // This is the m = 1 version of the complete residue rule; no `or` is needed.
    // Example: `forall x Z: x % 1 = 0`.
    pub(crate) fn try_verify_mod_one_equals_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let mod_obj = if Self::obj_is_builtin_literal_zero(left) {
            match right {
                Obj::Mod(m) => m,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_zero(right) {
            match left {
                Obj::Mod(m) => m,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_one(mod_obj.right.as_ref()) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: x % 1 = 0",
        )))
    }

    // First power identity: `a^1 = a`.
    // Example: `forall a Z: a^1 = a`.
    pub(crate) fn try_verify_pow_one_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (pow, other) = match (left, right) {
            (Obj::Pow(p), other) => (p, other),
            (other, Obj::Pow(p)) => (p, other),
            _ => return Ok(None),
        };
        if !Self::obj_is_builtin_literal_one(pow.exponent.as_ref()) {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                pow.base.as_ref(),
                other,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: a^1 = a",
        )))
    }

    // One as a base is invariant under exponentiation: `1^x = 1`.
    // This is used for simplifying powers with arbitrary well-defined exponents.
    // Example: `forall x R: 1^x = 1`.
    pub(crate) fn try_verify_one_pow_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let pow = if Self::obj_is_builtin_literal_one(left) {
            match right {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_one(right) {
            match left {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_one(pow.base.as_ref()) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: 1^x = 1",
        )))
    }

    // Zero as a base stays zero for positive exponents: `0^x = 0` when `x > 0`.
    // This is the real power rule used to avoid undefined cases such as `0^0`.
    // Example: `forall x R_pos: 0^x = 0`.
    pub(crate) fn try_verify_zero_pow_positive_exponent_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let pow = if Self::obj_is_builtin_literal_zero(left) {
            match right {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_zero(right) {
            match left {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_zero(pow.base.as_ref()) {
            return Ok(None);
        }

        let positive_exponent: AtomicFact = GreaterFact::new(
            (*pow.exponent).clone(),
            Self::literal_zero_obj_for_abs_builtin(),
            line_file.clone(),
        )
        .into();
        let positive_result = self.verify_non_equational_known_then_builtin_rules_only(
            &positive_exponent,
            verify_state,
        )?;
        if !positive_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: 0^x = 0 for x > 0".to_string(),
                vec![positive_result],
            )
            .into(),
        ))
    }

    // Principal square-root identity: `(sqrt(x))^2 = x` for real `x >= 0`.
    // Example: `forall x R: x >= 0 =>: (sqrt(x))^2 = x`.
    pub(crate) fn try_verify_sqrt_square_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (pow, other) = match (left, right) {
            (Obj::Pow(pow), other) => (pow, other),
            (other, Obj::Pow(pow)) => (pow, other),
            _ => return Ok(None),
        };
        if !Self::obj_is_builtin_literal_two(pow.exponent.as_ref()) {
            return Ok(None);
        }
        let Obj::Sqrt(sqrt) = pow.base.as_ref() else {
            return Ok(None);
        };
        let arg_result = self.verify_objs_are_equal_in_equality_builtin(
            sqrt.arg.as_ref(),
            other,
            line_file.clone(),
            verify_state,
        )?;
        if !arg_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "sqrt: (sqrt(x))^2 = x".to_string(),
                vec![arg_result],
            )
            .into(),
        ))
    }

    // Square roots of the additive and multiplicative identities stay fixed.
    // Example: `sqrt(0) = 0` and `sqrt(1) = 1`.
    pub(crate) fn try_verify_sqrt_zero_one_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (sqrt, other) = match (left, right) {
            (Obj::Sqrt(sqrt), other) => (sqrt, other),
            (other, Obj::Sqrt(sqrt)) => (sqrt, other),
            _ => return Ok(None),
        };
        for literal in [
            Number::new("0".to_string()).into(),
            Number::new("1".to_string()).into(),
        ] {
            let arg_result = self.verify_objs_are_equal_in_equality_builtin(
                sqrt.arg.as_ref(),
                &literal,
                line_file.clone(),
                verify_state,
            )?;
            if !arg_result.is_true() {
                continue;
            }
            let other_result = self.verify_objs_are_equal_in_equality_builtin(
                other,
                &literal,
                line_file.clone(),
                verify_state,
            )?;
            if !other_result.is_true() {
                continue;
            }
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "sqrt: sqrt(0) = 0 and sqrt(1) = 1".to_string(),
                    vec![arg_result, other_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    pub(crate) fn try_verify_sqrt_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_sqrt_square_identity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_sqrt_zero_one_identity(left, right, line_file, verify_state)?
        {
            return Ok(Some(done));
        }
        Ok(None)
    }

    fn obj_is_builtin_literal_two(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "2",
            _ => false,
        }
    }

    fn power_factor_matches_base_and_exponent(
        &mut self,
        factor: &Obj,
        base: &Obj,
        exponent: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Pow(pow) = factor else {
            if !Self::obj_is_builtin_literal_one(exponent) {
                return Ok(false);
            }
            return Ok(self
                .verify_objs_are_equal_in_equality_builtin(
                    base,
                    factor,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true());
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                base,
                pow.base.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(false);
        }
        Ok(self
            .verify_objs_are_equal_in_equality_builtin(
                exponent,
                pow.exponent.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true())
    }

    fn obj_is_verified_in_n_pos(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let in_n_pos: AtomicFact =
            InFact::new(obj.clone(), StandardSet::NPos.into(), line_file).into();
        Ok(self
            .verify_non_equational_known_then_builtin_rules_only(&in_n_pos, verify_state)?
            .is_true())
    }

    fn power_addition_exponent_rule_holds_one_direction(
        &mut self,
        combined_power: &Pow,
        product: &Mul,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Add(add_exponent) = combined_power.exponent.as_ref() else {
            return Ok(false);
        };

        // Power law for positive integer exponents:
        // `a^(m+n) = a^m * a^n`. Example: `forall a R, m, n N_pos: a^(m+n) = a^m * a^n`.
        let candidates = [
            (
                product.left.as_ref(),
                product.right.as_ref(),
                add_exponent.left.as_ref(),
                add_exponent.right.as_ref(),
            ),
            (
                product.right.as_ref(),
                product.left.as_ref(),
                add_exponent.left.as_ref(),
                add_exponent.right.as_ref(),
            ),
        ];

        for (left_factor, right_factor, left_exp, right_exp) in candidates {
            if !self.power_factor_matches_base_and_exponent(
                left_factor,
                combined_power.base.as_ref(),
                left_exp,
                line_file.clone(),
                verify_state,
            )? {
                continue;
            }
            if !self.power_factor_matches_base_and_exponent(
                right_factor,
                combined_power.base.as_ref(),
                right_exp,
                line_file.clone(),
                verify_state,
            )? {
                continue;
            }
            if !self.obj_is_verified_in_n_pos(left_exp, line_file.clone(), verify_state)? {
                return Ok(false);
            }
            if !self.obj_is_verified_in_n_pos(right_exp, line_file.clone(), verify_state)? {
                return Ok(false);
            }
            return Ok(true);
        }

        Ok(false)
    }

    pub(crate) fn try_verify_power_addition_exponent_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let holds = match (left, right) {
            (Obj::Pow(pow), Obj::Mul(product)) => self
                .power_addition_exponent_rule_holds_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    verify_state,
                )?,
            (Obj::Mul(product), Obj::Pow(pow)) => self
                .power_addition_exponent_rule_holds_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    verify_state,
                )?,
            _ => false,
        };
        if holds {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: a^(m+n) = a^m * a^n for m,n in N_pos",
            )));
        }
        Ok(None)
    }

    fn verify_context_arg_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        Ok(self
            .verify_objs_are_equal_in_equality_builtin(left, right, line_file, verify_state)?
            .is_true())
    }

    // If equal objects appear in the same algebraic context, the whole context is equal.
    // Example: from `x = y`, infer `x + 1 = y + 1`.
    pub(crate) fn try_verify_same_algebra_context_by_equal_args(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let args_equal = match (left, right) {
            (Obj::Add(l), Obj::Add(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Sub(l), Obj::Sub(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Mul(l), Obj::Mul(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Div(l), Obj::Div(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Mod(l), Obj::Mod(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Pow(l), Obj::Pow(r)) => {
                self.verify_context_arg_equality(
                    l.base.as_ref(),
                    r.base.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.exponent.as_ref(),
                    r.exponent.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            _ => return Ok(None),
        };
        if !args_equal {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: same algebraic context with equal arguments",
        )))
    }

    // log_a(a^b) = b  (Litex `log(a, a^b) = b`; same base in log and in the power.)
    pub(crate) fn try_verify_log_identity_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };

        if let Obj::Pow(p) = log.arg.as_ref() {
            let base_ok = self.verify_objs_are_equal_in_equality_builtin(
                p.base.as_ref(),
                log.base.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if base_ok.is_true() {
                let exp_ok = self.verify_objs_are_equal_in_equality_builtin(
                    p.exponent.as_ref(),
                    other,
                    line_file.clone(),
                    verify_state,
                )?;
                if exp_ok.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: log(a, a^b) = b",
                    )));
                }
            }
        }

        Ok(None)
    }

    // log_{a^b}(c) = log_a(c) / b  (Litex `log(a^b, c) = log(a, c) / b`; need b != 0 for a valid base.)
    fn try_verify_log_base_power_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Pow(p) = log.base.as_ref() else {
            return Ok(None);
        };
        let inner_log: Obj = Log::new((*p.base).clone(), (*log.arg).clone()).into();
        let expected: Obj = Div::new(inner_log, (*p.exponent).clone()).into();
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            other,
            &expected,
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: log(a^b, c) = log(a, c) / b",
            )));
        }
        Ok(None)
    }

    // log_a(x^b) = b * log_a(x)  (Litex `log(a, x^b) = b * log(a, x)`.)
    fn try_verify_log_arg_power_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Pow(p) = log.arg.as_ref() else {
            return Ok(None);
        };
        let inner_log: Obj = Log::new((*log.base).clone(), (*p.base).clone()).into();
        let expected1: Obj = Mul::new((*p.exponent).clone(), inner_log.clone()).into();
        let expected2: Obj = Mul::new(inner_log, (*p.exponent).clone()).into();
        for expected in [expected1, expected2] {
            let inner = self.verify_objs_are_equal_in_equality_builtin(
                other,
                &expected,
                line_file.clone(),
                verify_state,
            )?;
            if inner.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x^b) = b * log(a, x)",
                )));
            }
        }
        Ok(None)
    }

    // log_a(x y) = log_a(x) + log_a(y)  (Litex `log(a, x*y) = log(a, x) + log(a, y)`.)
    fn try_verify_log_product_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Mul(m) = log.arg.as_ref() else {
            return Ok(None);
        };
        let l1: Obj = Log::new((*log.base).clone(), (*m.left).clone()).into();
        let l2: Obj = Log::new((*log.base).clone(), (*m.right).clone()).into();
        let expected1: Obj = Add::new(l1.clone(), l2.clone()).into();
        let expected2: Obj = Add::new(l2, l1).into();
        for expected in [expected1, expected2] {
            let inner = self.verify_objs_are_equal_in_equality_builtin(
                other,
                &expected,
                line_file.clone(),
                verify_state,
            )?;
            if inner.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x*y) = log(a, x) + log(a, y)",
                )));
            }
        }
        Ok(None)
    }

    // log_a(x / y) = log_a(x) - log_a(y)  (Litex `log(a, x/y) = log(a, x) - log(a, y)`.)
    fn try_verify_log_quotient_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Div(d) = log.arg.as_ref() else {
            return Ok(None);
        };
        let l1: Obj = Log::new((*log.base).clone(), (*d.left).clone()).into();
        let l2: Obj = Log::new((*log.base).clone(), (*d.right).clone()).into();
        let expected = Sub::new(l1, l2).into();
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            other,
            &expected,
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: log(a, x/y) = log(a, x) - log(a, y)",
            )));
        }
        Ok(None)
    }

    // Algebraic log rules: log_{a^b}(c), log_a(x^b), log_a(x y), log_a(x / y) (see functions above).
    pub(crate) fn try_verify_log_algebra_identities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_log_base_power_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_log_arg_power_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_log_product_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_log_quotient_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        Ok(None)
    }

    // Reciprocal rule: log_a(1 / x) = -log_a(x).
    // Example: `forall a, x R_pos: a != 1 =>: log(a, 1 / x) = -log(a, x)`.
    pub(crate) fn try_verify_log_reciprocal_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Div(d) = log.arg.as_ref() else {
            return Ok(None);
        };
        let one = Self::literal_one_obj_for_log_builtin();
        let one_ok = self.verify_objs_are_equal_in_equality_builtin(
            d.left.as_ref(),
            &one,
            line_file.clone(),
            verify_state,
        )?;
        if !one_ok.is_true() {
            return Ok(None);
        }

        let inner_log: Obj = Log::new((*log.base).clone(), (*d.right).clone()).into();
        let expected1: Obj = Mul::new(
            Self::literal_neg_one_obj_for_log_builtin(),
            inner_log.clone(),
        )
        .into();
        let expected2: Obj = Mul::new(
            inner_log.clone(),
            Self::literal_neg_one_obj_for_log_builtin(),
        )
        .into();
        let expected3: Obj = Sub::new(Self::literal_zero_obj_for_abs_builtin(), inner_log).into();

        for expected in [expected1, expected2, expected3] {
            let ok = self.verify_objs_are_equal_in_equality_builtin(
                other,
                &expected,
                line_file.clone(),
                verify_state,
            )?;
            if ok.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: log(a, 1/x) = -log(a, x)",
                )));
            }
        }

        Ok(None)
    }

    // Change of base: log_a(b) = log_c(b) / log_c(a).
    // Example: `forall a, b, c R_pos: a != 1, c != 1 =>: log(a, b) = log(c, b) / log(c, a)`.
    pub(crate) fn try_verify_log_change_of_base_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log_ab, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Div(d) = other else {
            return Ok(None);
        };
        let (Obj::Log(log_cb), Obj::Log(log_ca)) = (d.left.as_ref(), d.right.as_ref()) else {
            return Ok(None);
        };

        let base_ok = self.verify_objs_are_equal_in_equality_builtin(
            log_cb.base.as_ref(),
            log_ca.base.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !base_ok.is_true() {
            return Ok(None);
        }
        let arg_ok = self.verify_objs_are_equal_in_equality_builtin(
            log_cb.arg.as_ref(),
            log_ab.arg.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !arg_ok.is_true() {
            return Ok(None);
        }
        let inner_ok = self.verify_objs_are_equal_in_equality_builtin(
            log_ca.arg.as_ref(),
            log_ab.base.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !inner_ok.is_true() {
            return Ok(None);
        }

        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: log(a, b) = log(c, b) / log(c, a)",
        )))
    }

    // log_a(b) = c  iff  a^c = b  (Litex `log(a, b) = c`; reduces to proving `a^c = b`.)
    pub(crate) fn try_verify_log_equals_by_pow_inverse(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let pow_obj: Obj = Pow::new((*log.base).clone(), other.clone()).into();
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            &pow_obj,
            log.arg.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: log(a, b) = c from a^c = b",
            )));
        }
        Ok(None)
    }

    // Exponential inverse in the other direction: a^c = b from known c = log_a(b).
    // Example: `forall a, b R_pos, c R: log(a, b) = c =>: a^c = b`.
    pub(crate) fn try_verify_pow_equals_by_known_log_inverse(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (pow, other) = match (left, right) {
            (Obj::Pow(p), o) => (p, o),
            (o, Obj::Pow(p)) => (p, o),
            _ => return Ok(None),
        };
        let expected_log: Obj = Log::new((*pow.base).clone(), other.clone()).into();
        let exponent_ok = self.verify_objs_are_equal_known_only(
            pow.exponent.as_ref(),
            &expected_log,
            line_file.clone(),
        );
        if !exponent_ok.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: a^c = b from c = log(a, b)".to_string(),
                vec![exponent_ok],
            )
            .into(),
        ))
    }

    /// `sum(s,e,f) = sum(s,e,g) + sum(s,e,h)` when for all integer `x` with `s <= x <= e`,
    /// `f(x) = g(x) + h(x)` (summands are unary anonymous `fn` bodies, instantiated at `x`).
    pub(crate) fn try_verify_sum_additivity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }

        let (sum_m, sum_a, sum_b) = match (left, right) {
            (Obj::Sum(m), Obj::Add(a)) => match (a.left.as_ref(), a.right.as_ref()) {
                (Obj::Sum(a1), Obj::Sum(a2)) => (m, a1, a2),
                _ => return Ok(None),
            },
            (Obj::Add(a), Obj::Sum(m)) => match (a.left.as_ref(), a.right.as_ref()) {
                (Obj::Sum(a1), Obj::Sum(a2)) => (m, a1, a2),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };

        let mut require_eq = |a: &Obj, b: &Obj| -> Result<bool, RuntimeError> {
            Ok(self
                .verify_objs_are_equal_in_equality_builtin(a, b, line_file.clone(), verify_state)?
                .is_true())
        };
        if !require_eq(sum_m.start.as_ref(), sum_a.start.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.start.as_ref(), sum_b.start.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.end.as_ref(), sum_a.end.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.end.as_ref(), sum_b.end.as_ref())? {
            return Ok(None);
        }

        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);

        let Some(l_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_m.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(a_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_a.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(b_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_b.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let then_fact: ExistOrAndChainAtomicFact =
            EqualFact::new(l_inst, Add::new(a_inst, b_inst).into(), line_file.clone()).into();

        let dom_lo: Fact =
            LessEqualFact::new((*sum_m.start).clone(), x_obj.clone(), line_file.clone()).into();
        let dom_hi: Fact =
            LessEqualFact::new(x_obj.clone(), (*sum_m.end).clone(), line_file.clone()).into();

        let forall_fact: Fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_name],
                ParamType::Obj(StandardSet::Z.into()),
            )]),
            vec![dom_lo, dom_hi],
            vec![then_fact],
            line_file.clone(),
        )?
        .into();

        let r = self.verify_fact(&forall_fact, verify_state)?;
        if r.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: sum additivity from pointwise equality on the integer index range",
            )));
        }
        Ok(None)
    }

    fn instantiate_unary_anonymous_summand_at(
        &mut self,
        func: &Obj,
        x: &Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        let af: &AnonymousFn = match func {
            Obj::AnonymousFn(af) => af,
            Obj::FnObj(fo) => {
                if !fo.body.is_empty() {
                    return Ok(None);
                }
                match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let param_defs = &af.body.params_def_with_set;
        let args = vec![x.clone()];
        let param_to_arg_map =
            ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(param_defs, &args);
        Ok(Some(self.inst_obj(
            af.equal_to.as_ref(),
            &param_to_arg_map,
            ParamObjType::FnSet,
        )?))
    }

    /// `sum(a..b) + sum((b+1)..c) = sum(a..c)` with the same unary anonymous summand on each side.
    pub(crate) fn try_verify_sum_merge_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (add, s3) = match (left, right) {
            (Obj::Add(a), Obj::Sum(s)) => (a, s),
            (Obj::Sum(s), Obj::Add(a)) => (a, s),
            _ => return Ok(None),
        };
        let (s1, s2) = match (add.left.as_ref(), add.right.as_ref()) {
            (Obj::Sum(x), Obj::Sum(y)) => (x, y),
            _ => return Ok(None),
        };
        for (a, b) in [(s1, s2), (s2, s1)] {
            if let Some(done) = self.try_verify_sum_merge_ordered_pair(
                a,
                b,
                s3,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    fn try_verify_sum_merge_ordered_pair(
        &mut self,
        s1: &Sum,
        s2: &Sum,
        s3: &Sum,
        stmt_left: &Obj,
        stmt_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        let gap = Add::new((*s1.end).clone(), one).into();
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &gap,
                s2.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.start.as_ref(),
                s3.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s2.end.as_ref(),
                s3.end.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.func.as_ref(),
                s2.func.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.func.as_ref(),
                s3.func.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            stmt_left,
            stmt_right,
            line_file,
            "equality: merge adjacent sum ranges with the same summand",
        )))
    }

    // A finite sum over one index is the summand at that index.
    // Example: `sum(1, 1, 'N_pos(x){x}) = 1`.
    pub(crate) fn try_verify_sum_single_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (sum_obj, other) in [(left, right), (right, left)] {
            let Obj::Sum(sum) = sum_obj else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    sum.start.as_ref(),
                    sum.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let Some(expected) =
                self.instantiate_unary_anonymous_summand_at(sum.func.as_ref(), sum.start.as_ref())?
            else {
                continue;
            };
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    &expected,
                    other,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: single-term sum equals the summand",
                )));
            }
        }
        Ok(None)
    }

    // A finite product over one index is the factor at that index.
    // Example: `product(1, 1, 'N_pos(x){x}) = 1`.
    pub(crate) fn try_verify_product_single_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (product_obj, other) in [(left, right), (right, left)] {
            let Obj::Product(product) = product_obj else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    product.start.as_ref(),
                    product.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let Some(expected) = self.instantiate_unary_anonymous_summand_at(
                product.func.as_ref(),
                product.start.as_ref(),
            )?
            else {
                continue;
            };
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    &expected,
                    other,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: single-term product equals the factor",
                )));
            }
        }
        Ok(None)
    }

    // sum(s,e,f) = sum(s,e-1,f) + f(e): same unary summand, shared start, e = (e-1)+1 on the shorter range.
    pub(crate) fn try_verify_sum_split_last_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_obj, add_obj) in [(left, right), (right, left)] {
            let Obj::Sum(s_full) = full_obj else {
                continue;
            };
            let Obj::Add(a) = add_obj else {
                continue;
            };
            for (sum_part, tail) in [
                (a.left.as_ref(), a.right.as_ref()),
                (a.right.as_ref(), a.left.as_ref()),
            ] {
                let Obj::Sum(s_pre) = sum_part else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.start.as_ref(),
                        s_pre.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let end_pre_plus_one: Obj = Add::new((*s_pre.end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.func.as_ref(),
                        s_pre.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let Some(expected_tail) = self.instantiate_unary_anonymous_summand_at(
                    s_full.func.as_ref(),
                    s_full.end.as_ref(),
                )?
                else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &expected_tail,
                        tail,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum through e equals sum through e-1 plus last summand f(e)",
                )));
            }
        }
        Ok(None)
    }

    // product(s,e,f) = product(s,e-1,f) * f(e): same unary factor, shared start, e = (e-1)+1.
    pub(crate) fn try_verify_product_split_last_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_obj, mul_obj) in [(left, right), (right, left)] {
            let Obj::Product(p_full) = full_obj else {
                continue;
            };
            let Obj::Mul(m) = mul_obj else {
                continue;
            };
            for (prod_part, tail) in [
                (m.left.as_ref(), m.right.as_ref()),
                (m.right.as_ref(), m.left.as_ref()),
            ] {
                let Obj::Product(p_pre) = prod_part else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.start.as_ref(),
                        p_pre.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let end_pre_plus_one: Obj = Add::new((*p_pre.end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.func.as_ref(),
                        p_pre.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let Some(expected_tail) = self.instantiate_unary_anonymous_summand_at(
                    p_full.func.as_ref(),
                    p_full.end.as_ref(),
                )?
                else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &expected_tail,
                        tail,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: product through e equals product through e-1 times last factor f(e)",
                )));
            }
        }
        Ok(None)
    }

    fn flatten_left_assoc_add_chain(obj: &Obj) -> Vec<&Obj> {
        match obj {
            Obj::Add(a) => {
                let mut v = Self::flatten_left_assoc_add_chain(a.left.as_ref());
                v.push(a.right.as_ref());
                v
            }
            _ => vec![obj],
        }
    }

    fn flatten_left_assoc_mul_chain(obj: &Obj) -> Vec<&Obj> {
        match obj {
            Obj::Mul(m) => {
                let mut v = Self::flatten_left_assoc_mul_chain(m.left.as_ref());
                v.push(m.right.as_ref());
                v
            }
            _ => vec![obj],
        }
    }

    // sum(s,e,f) = sum(s1,e1,f) + sum(s2,e2,f) + ... with contiguous [si,ei] tiling [s,e], same unary f.
    pub(crate) fn try_verify_sum_partition_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_side, add_side) in [(left, right), (right, left)] {
            let Obj::Sum(s_full) = full_side else {
                continue;
            };
            let Obj::Add(_) = add_side else {
                continue;
            };
            let parts = Self::flatten_left_assoc_add_chain(add_side);
            if parts.len() < 2 {
                continue;
            }
            let mut sums: Vec<&Sum> = Vec::with_capacity(parts.len());
            let mut all_sum = true;
            for p in &parts {
                if let Obj::Sum(s) = p {
                    sums.push(s);
                } else {
                    all_sum = false;
                    break;
                }
            }
            if !all_sum {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s_full.start.as_ref(),
                    sums[0].start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s_full.end.as_ref(),
                    sums[sums.len() - 1].end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let mut gaps_ok = true;
            for i in 0..sums.len().saturating_sub(1) {
                let gap = Add::new((*sums[i].end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &gap,
                        sums[i + 1].start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    gaps_ok = false;
                    break;
                }
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for s in &sums {
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.func.as_ref(),
                        s.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    func_ok = false;
                    break;
                }
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: sum partitions closed range into adjacent sub-sums with the same summand",
            )));
        }
        Ok(None)
    }

    // product(s,e,f) = product(s1,e1,f) * product(s2,e2,f) * ... contiguous tiling, same unary f.
    pub(crate) fn try_verify_product_partition_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_side, mul_side) in [(left, right), (right, left)] {
            let Obj::Product(p_full) = full_side else {
                continue;
            };
            let Obj::Mul(_) = mul_side else {
                continue;
            };
            let parts = Self::flatten_left_assoc_mul_chain(mul_side);
            if parts.len() < 2 {
                continue;
            }
            let mut products: Vec<&Product> = Vec::with_capacity(parts.len());
            let mut all_prod = true;
            for p in &parts {
                if let Obj::Product(pr) = p {
                    products.push(pr);
                } else {
                    all_prod = false;
                    break;
                }
            }
            if !all_prod {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p_full.start.as_ref(),
                    products[0].start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p_full.end.as_ref(),
                    products[products.len() - 1].end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let mut gaps_ok = true;
            for i in 0..products.len().saturating_sub(1) {
                let gap = Add::new((*products[i].end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &gap,
                        products[i + 1].start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    gaps_ok = false;
                    break;
                }
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for p in &products {
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.func.as_ref(),
                        p.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    func_ok = false;
                    break;
                }
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: product partitions closed range into adjacent sub-products with the same factor",
            )));
        }
        Ok(None)
    }

    /// `sum(L) = sum(R)` with `R` a translate of `L` by `k` on both bounds, reduced to pointwise
    /// equality on the right-hand index range.
    pub(crate) fn try_verify_sum_reindex_shift(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (l_obj, r_obj) in [(left, right), (right, left)] {
            let (Obj::Sum(l_sum), Obj::Sum(r_sum)) = (l_obj, r_obj) else {
                continue;
            };
            let k: Obj = Sub::new((*r_sum.start).clone(), (*l_sum.start).clone()).into();
            let k_end = Sub::new((*r_sum.end).clone(), (*l_sum.end).clone()).into();
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    &k,
                    &k_end,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let y_name = self.generate_random_unused_name();
            let y_obj = obj_for_bound_param_in_scope(y_name.clone(), ParamObjType::Forall);
            let index_for_left = Sub::new(y_obj.clone(), k.clone()).into();
            let Some(at_l) =
                self.instantiate_unary_anonymous_summand_at(l_sum.func.as_ref(), &index_for_left)?
            else {
                continue;
            };
            let Some(at_r) =
                self.instantiate_unary_anonymous_summand_at(r_sum.func.as_ref(), &y_obj)?
            else {
                continue;
            };
            let then_fact: ExistOrAndChainAtomicFact =
                EqualFact::new(at_l, at_r, line_file.clone()).into();
            let dom_lo: Fact =
                LessEqualFact::new((*r_sum.start).clone(), y_obj.clone(), line_file.clone()).into();
            let dom_hi: Fact =
                LessEqualFact::new(y_obj.clone(), (*r_sum.end).clone(), line_file.clone()).into();
            let forall_fact: Fact = ForallFact::new(
                ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![y_name],
                    ParamType::Obj(StandardSet::Z.into()),
                )]),
                vec![dom_lo, dom_hi],
                vec![then_fact],
                line_file.clone(),
            )?
            .into();
            let r = self.verify_fact(&forall_fact, verify_state)?;
            if r.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum reindexing (integer shift) from pointwise equality on the range",
                )));
            }
        }
        Ok(None)
    }

    /// `sum(s,e, \lambda x.c) = (e - s + 1) * c` when `c` does not mention the index parameter.
    pub(crate) fn try_verify_sum_constant_summand(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::Sum(s) = sum_side else {
                continue;
            };
            let af = match s.func.as_ref() {
                Obj::AnonymousFn(af) => af,
                Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => continue,
                },
                _ => continue,
            };
            if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
                continue;
            }
            let names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
            let pname = match names.first() {
                Some(n) => n.as_str(),
                None => continue,
            };
            if obj_expr_mentions_bare_id(af.equal_to.as_ref(), pname) {
                continue;
            }
            let c = (*af.equal_to).clone();
            let one: Obj = Number::new("1".to_string()).into();
            let count: Obj =
                Add::new(Sub::new((*s.end).clone(), (*s.start).clone()).into(), one).into();
            let m1: Obj = Mul::new(count.clone(), c.clone()).into();
            let m2: Obj = Mul::new(c, count).into();
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &m1,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
                || self
                    .verify_objs_are_equal_in_equality_builtin(
                        other,
                        &m2,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum of a constant summand over a closed integer range",
                )));
            }
        }
        Ok(None)
    }

    /// `(x mod m) mod m = x mod m` when the nested `%` uses the same modulus as the outer `%`.
    ///
    /// Used to match residues after reducing summands: e.g. prove `X % Z = (X % Z) % Z` so
    /// `(X+Y)%Z = ((X%Z)+(Y%Z))%Z` can close via congruence.
    pub(crate) fn try_verify_mod_nested_same_modulus_absorption(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (side_nested, side_simple) in [(left, right), (right, left)] {
            let Obj::Mod(outer) = side_nested else {
                continue;
            };
            let Obj::Mod(inner) = outer.left.as_ref() else {
                continue;
            };
            let Obj::Mod(simple) = side_simple else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    outer.right.as_ref(),
                    inner.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    outer.right.as_ref(),
                    simple.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    inner.left.as_ref(),
                    simple.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: nested mod with same modulus absorbs inner mod",
            )));
        }
        Ok(None)
    }

    // a % m = (b % m) % m reduces to a % m = b % m (same m); the inner equality must be known-only.
    pub(crate) fn try_verify_mod_peel_nested_same_modulus(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                lm.right.as_ref(),
                rm.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let modulus = lm.right.as_ref();

        if let Obj::Mod(r_inner) = rm.left.as_ref() {
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    r_inner.right.as_ref(),
                    modulus,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                let lhs: Obj = Mod::new((*lm.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*r_inner.left).clone(), (*lm.right).clone()).into();
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        &lhs,
                        &rhs,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
                    )));
                }
            }
        }

        if let Obj::Mod(l_inner) = lm.left.as_ref() {
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    l_inner.right.as_ref(),
                    modulus,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                let lhs: Obj = Mod::new((*l_inner.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*rm.left).clone(), (*lm.right).clone()).into();
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        &lhs,
                        &rhs,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
                    )));
                }
            }
        }

        Ok(None)
    }

    /// If `% m` agrees on both sides, congruence for `+`, `-`, `*` on integers: reduce to two residue
    /// equalities.
    ///
    /// Example: `(x + y) % m = (x' + y') % m` from `(x % m) = (x' % m)` and `(y % m) = (y' % m)`.
    pub(crate) fn try_verify_mod_congruence_from_inner_binary(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                lm.right.as_ref(),
                rm.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let mut pair_ok = |a: &Obj, b: &Obj| -> Result<bool, RuntimeError> {
            let l: Obj = Mod::new(a.clone(), (*lm.right).clone()).into();
            let r: Obj = Mod::new(b.clone(), (*rm.right).clone()).into();
            Ok(self
                .verify_objs_are_equal_in_equality_builtin(&l, &r, line_file.clone(), verify_state)?
                .is_true())
        };
        let ok = match (lm.left.as_ref(), rm.left.as_ref()) {
            (Obj::Add(la), Obj::Add(ra)) => {
                pair_ok(la.left.as_ref(), ra.left.as_ref())?
                    && pair_ok(la.right.as_ref(), ra.right.as_ref())?
            }
            (Obj::Sub(ls), Obj::Sub(rs)) => {
                pair_ok(ls.left.as_ref(), rs.left.as_ref())?
                    && pair_ok(ls.right.as_ref(), rs.right.as_ref())?
            }
            (Obj::Mul(lx), Obj::Mul(rx)) => {
                pair_ok(lx.left.as_ref(), rx.left.as_ref())?
                    && pair_ok(lx.right.as_ref(), rx.right.as_ref())?
            }
            _ => return Ok(None),
        };
        if !ok {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: integer congruence — same modulus, residues for matching + / - / *",
        )))
    }
}
