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

    fn literal_neg_one_obj_for_abs_builtin() -> Obj {
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

    fn neg_obj_for_abs_builtin(obj: &Obj) -> Obj {
        Mul::new(Self::literal_neg_one_obj_for_abs_builtin(), obj.clone()).into()
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

    // Absolute value is invariant under sign change.
    // Examples: `abs(x) = abs(-x)` and `abs(x - y) = abs(y - x)`.
    fn try_verify_abs_sign_invariance(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (left, right) else {
            return Ok(None);
        };
        let left_arg = left_abs.arg.as_ref();
        let right_arg = right_abs.arg.as_ref();
        let left_neg_right = Self::neg_obj_for_abs_builtin(right_arg);
        let right_neg_left = Self::neg_obj_for_abs_builtin(left_arg);
        if !Self::obj_is_negation_of_for_abs_builtin(left_arg, right_arg)
            && !Self::obj_is_negation_of_for_abs_builtin(right_arg, left_arg)
            && !objs_equal_by_rational_expression_evaluation(left_arg, &left_neg_right)
            && !objs_equal_by_rational_expression_evaluation(right_arg, &right_neg_left)
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "abs: abs(x) = abs(-x)",
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
        if let Some(done) = self.try_verify_abs_sign_invariance(left, right, line_file.clone())? {
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

    fn obj_is_builtin_literal_neg_one(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "-1",
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

        Ok(StmtResult::Unknown(StmtUnknown::new()))
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

    // 0 = a^n when n is a literal integer > 0 (does not rewrite 0^0 or 0^negative), from a = 0.
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

    // Subtracting the Euclidean remainder leaves a multiple of the positive modulus.
    // Example: `forall a Z, b N_pos: (a - a % b) % b = 0`.
    pub(crate) fn try_verify_mod_dividend_minus_remainder_equals_zero(
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
        let Obj::Mod(outer_mod) = target else {
            return Ok(None);
        };
        let Obj::Sub(sub) = outer_mod.left.as_ref() else {
            return Ok(None);
        };
        let Obj::Mod(inner_mod) = sub.right.as_ref() else {
            return Ok(None);
        };
        if !objs_equal_by_display_string(sub.left.as_ref(), inner_mod.left.as_ref()) {
            return Ok(None);
        }
        if !objs_equal_by_display_string(outer_mod.right.as_ref(), inner_mod.right.as_ref()) {
            return Ok(None);
        }

        let dividend_in_z: AtomicFact = InFact::new(
            sub.left.as_ref().clone(),
            StandardSet::Z.into(),
            line_file.clone(),
        )
        .into();
        let dividend_result =
            self.verify_non_equational_known_then_builtin_rules_only(&dividend_in_z, verify_state)?;
        if !dividend_result.is_true() {
            return Ok(None);
        }

        let modulus_in_n_pos: AtomicFact = InFact::new(
            outer_mod.right.as_ref().clone(),
            StandardSet::NPos.into(),
            line_file.clone(),
        )
        .into();
        let modulus_result = self
            .verify_non_equational_known_then_builtin_rules_only(&modulus_in_n_pos, verify_state)?;
        if !modulus_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: (a - a % b) % b = 0 for a in Z and b in N_pos".to_string(),
                vec![dividend_result, modulus_result],
            )
            .into(),
        ))
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

    // Zeroth power identity under the natural-exponent convention: `a^0 = 1`,
    // including `0^0 = 1`.
    // Example: `forall a R: a^0 = 1`.
    pub(crate) fn try_verify_pow_zero_identity(
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
        if !Self::obj_is_builtin_literal_zero(pow.exponent.as_ref()) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: a^0 = 1",
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
    // This intentionally does not cover the zeroth power convention `0^0 = 1`.
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

    // Equal nonnegative arguments have equal principal square roots.
    // Example: from `x = y`, prove `sqrt(x) = sqrt(y)`.
    pub(crate) fn try_verify_sqrt_equal_args_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Sqrt(left_sqrt), Obj::Sqrt(right_sqrt)) = (left, right) else {
            return Ok(None);
        };
        let arg_result = self.verify_objs_are_equal_in_equality_builtin(
            left_sqrt.arg.as_ref(),
            right_sqrt.arg.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !arg_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "sqrt: sqrt(x) = sqrt(y) from x = y".to_string(),
                vec![arg_result],
            )
            .into(),
        ))
    }

    // Principal square root of a square returns the nonnegative root.
    // Example: from `a >= 0` and `x = a^2`, prove `sqrt(x) = a`.
    pub(crate) fn try_verify_sqrt_of_square_identity(
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

        let nonnegative: AtomicFact = LessEqualFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            other.clone(),
            line_file.clone(),
        )
        .into();
        let nonnegative_result =
            self.verify_non_equational_known_then_builtin_rules_only(&nonnegative, verify_state)?;
        if !nonnegative_result.is_true() {
            return Ok(None);
        }

        let other_squared: Obj =
            Pow::new(other.clone(), Number::new("2".to_string()).into()).into();
        let square_result = self.verify_objs_are_equal_in_equality_builtin(
            sqrt.arg.as_ref(),
            &other_squared,
            line_file.clone(),
            verify_state,
        )?;
        if !square_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "sqrt: sqrt(a^2) = a for a >= 0".to_string(),
                vec![nonnegative_result, square_result],
            )
            .into(),
        ))
    }

    // Square root distributes over products of nonnegative factors.
    // Example: from `a >= 0`, `b >= 0`, and `x = a * b`, prove
    // `sqrt(x) = sqrt(a) * sqrt(b)`.
    pub(crate) fn try_verify_sqrt_product_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (sqrt, product) = match (left, right) {
            (Obj::Sqrt(sqrt), Obj::Mul(product)) => (sqrt, product),
            (Obj::Mul(product), Obj::Sqrt(sqrt)) => (sqrt, product),
            _ => return Ok(None),
        };
        let (Obj::Sqrt(left_factor), Obj::Sqrt(right_factor)) =
            (product.left.as_ref(), product.right.as_ref())
        else {
            return Ok(None);
        };

        let left_nonnegative: AtomicFact = LessEqualFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            left_factor.arg.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let left_nonnegative_result = self
            .verify_non_equational_known_then_builtin_rules_only(&left_nonnegative, verify_state)?;
        if !left_nonnegative_result.is_true() {
            return Ok(None);
        }

        let right_nonnegative: AtomicFact = LessEqualFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            right_factor.arg.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let right_nonnegative_result = self.verify_non_equational_known_then_builtin_rules_only(
            &right_nonnegative,
            verify_state,
        )?;
        if !right_nonnegative_result.is_true() {
            return Ok(None);
        }

        let arg_product: Obj = Mul::new(
            left_factor.arg.as_ref().clone(),
            right_factor.arg.as_ref().clone(),
        )
        .into();
        let arg_product_result = self.verify_objs_are_equal_in_equality_builtin(
            sqrt.arg.as_ref(),
            &arg_product,
            line_file.clone(),
            verify_state,
        )?;
        if !arg_product_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "sqrt: sqrt(a * b) = sqrt(a) * sqrt(b)".to_string(),
                vec![
                    left_nonnegative_result,
                    right_nonnegative_result,
                    arg_product_result,
                ],
            )
            .into(),
        ))
    }

    // Square root distributes over quotients with nonnegative numerator and positive denominator.
    // Example: from `a >= 0`, `b > 0`, and `x = a / b`, prove
    // `sqrt(x) = sqrt(a) / sqrt(b)`.
    pub(crate) fn try_verify_sqrt_quotient_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (sqrt, quotient) = match (left, right) {
            (Obj::Sqrt(sqrt), Obj::Div(quotient)) => (sqrt, quotient),
            (Obj::Div(quotient), Obj::Sqrt(sqrt)) => (sqrt, quotient),
            _ => return Ok(None),
        };
        let (Obj::Sqrt(numerator_sqrt), Obj::Sqrt(denominator_sqrt)) =
            (quotient.left.as_ref(), quotient.right.as_ref())
        else {
            return Ok(None);
        };

        let numerator_nonnegative: AtomicFact = LessEqualFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            numerator_sqrt.arg.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let numerator_nonnegative_result = self
            .verify_non_equational_known_then_builtin_rules_only(
                &numerator_nonnegative,
                verify_state,
            )?;
        if !numerator_nonnegative_result.is_true() {
            return Ok(None);
        }

        let denominator_positive: AtomicFact = LessFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            denominator_sqrt.arg.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let denominator_positive_result = self
            .verify_non_equational_known_then_builtin_rules_only(
                &denominator_positive,
                verify_state,
            )?;
        if !denominator_positive_result.is_true() {
            return Ok(None);
        }

        let arg_quotient: Obj = Div::new(
            numerator_sqrt.arg.as_ref().clone(),
            denominator_sqrt.arg.as_ref().clone(),
        )
        .into();
        let arg_quotient_result = self.verify_objs_are_equal_in_equality_builtin(
            sqrt.arg.as_ref(),
            &arg_quotient,
            line_file.clone(),
            verify_state,
        )?;
        if !arg_quotient_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "sqrt: sqrt(a / b) = sqrt(a) / sqrt(b)".to_string(),
                vec![
                    numerator_nonnegative_result,
                    denominator_positive_result,
                    arg_quotient_result,
                ],
            )
            .into(),
        ))
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
            self.try_verify_sqrt_zero_one_identity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_sqrt_equal_args_identity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_sqrt_of_square_identity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_sqrt_product_identity(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_sqrt_quotient_identity(left, right, line_file, verify_state)?
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

    fn obj_is_verified_in_standard_set_for_power_builtin(
        &mut self,
        obj: &Obj,
        standard_set: StandardSet,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let in_set: AtomicFact = InFact::new(obj.clone(), standard_set.into(), line_file).into();
        Ok(self
            .verify_non_equational_known_then_builtin_rules_only(&in_set, verify_state)?
            .is_true())
    }

    fn obj_is_verified_integer_exponent_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        if self.obj_is_verified_in_standard_set_for_power_builtin(
            obj,
            StandardSet::Z,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(true);
        }
        self.obj_is_verified_in_standard_set_for_power_builtin(
            obj,
            StandardSet::N,
            line_file,
            verify_state,
        )
    }

    fn obj_is_verified_nonzero_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let nonzero: AtomicFact = NotEqualFact::new(
            obj.clone(),
            Self::literal_zero_obj_for_abs_builtin(),
            line_file,
        )
        .into();
        Ok(self
            .verify_non_equational_known_then_builtin_rules_only(&nonzero, verify_state)?
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
            let exponents_are_positive =
                self.obj_is_verified_in_n_pos(left_exp, line_file.clone(), verify_state)?
                    && self.obj_is_verified_in_n_pos(right_exp, line_file.clone(), verify_state)?;
            if exponents_are_positive {
                return Ok(true);
            }

            // Natural-exponent power law for real bases:
            // `a^(m+n) = a^m * a^n`, including the cases m=0 or n=0.
            // Example: `forall a R, m, n N: a^m * a^n = a^(m+n)`.
            let exponents_are_natural = self.obj_is_verified_in_standard_set_for_power_builtin(
                left_exp,
                StandardSet::N,
                line_file.clone(),
                verify_state,
            )? && self
                .obj_is_verified_in_standard_set_for_power_builtin(
                    right_exp,
                    StandardSet::N,
                    line_file.clone(),
                    verify_state,
                )?;
            if exponents_are_natural {
                let base_in_r = self.obj_is_verified_in_standard_set_for_power_builtin(
                    combined_power.base.as_ref(),
                    StandardSet::R,
                    line_file.clone(),
                    verify_state,
                )?;
                if base_in_r {
                    return Ok(true);
                }
            }

            // The remaining integer-exponent branch needs a nonzero base so negative
            // exponents do not accidentally justify undefined `0^(-n)`.
            // Example: `forall a R_nz, m, n Z: a^m * a^n = a^(m+n)`.
            let exponents_are_integer = self.obj_is_verified_integer_exponent_for_power_builtin(
                left_exp,
                line_file.clone(),
                verify_state,
            )? && self
                .obj_is_verified_integer_exponent_for_power_builtin(
                    right_exp,
                    line_file.clone(),
                    verify_state,
                )?;
            if !exponents_are_integer {
                return Ok(false);
            }
            if !self.obj_is_verified_nonzero_for_power_builtin(
                combined_power.base.as_ref(),
                line_file.clone(),
                verify_state,
            )? {
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
                "equality: a^(m+n) = a^m * a^n for natural exponents over real bases, positive exponents, or integer exponents with nonzero base",
            )));
        }
        Ok(None)
    }

    fn power_of_power_rule_holds_one_direction(
        &mut self,
        nested_power: &Pow,
        combined_power: &Pow,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Pow(inner_power) = nested_power.base.as_ref() else {
            return Ok(false);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                inner_power.base.as_ref(),
                combined_power.base.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(false);
        }

        let multiplied_exponent: Obj = Mul::new(
            inner_power.exponent.as_ref().clone(),
            nested_power.exponent.as_ref().clone(),
        )
        .into();
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &multiplied_exponent,
                combined_power.exponent.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(false);
        }

        // Power-of-power law for positive integer exponents:
        // `(a^m)^n = a^(m*n)`. Example: `forall a R, m, n N_pos: (a^m)^n = a^(m*n)`.
        let exponents_are_positive = self.obj_is_verified_in_n_pos(
            inner_power.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )? && self.obj_is_verified_in_n_pos(
            nested_power.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if exponents_are_positive {
            return Ok(true);
        }

        // Natural-exponent power-of-power law over real bases, including zero exponents.
        // Example: `forall a R, m, n N: (a^m)^n = a^(m*n)`.
        let exponents_are_natural = self.obj_is_verified_in_standard_set_for_power_builtin(
            inner_power.exponent.as_ref(),
            StandardSet::N,
            line_file.clone(),
            verify_state,
        )? && self.obj_is_verified_in_standard_set_for_power_builtin(
            nested_power.exponent.as_ref(),
            StandardSet::N,
            line_file.clone(),
            verify_state,
        )?;
        if exponents_are_natural
            && self.obj_is_verified_in_standard_set_for_power_builtin(
                combined_power.base.as_ref(),
                StandardSet::R,
                line_file.clone(),
                verify_state,
            )?
        {
            return Ok(true);
        }

        // Integer-exponent power-of-power law needs a nonzero base so negative
        // exponents do not justify undefined powers of zero.
        // Example: `forall a R_nz, m, n Z: (a^m)^n = a^(m*n)`.
        let exponents_are_integer = self.obj_is_verified_integer_exponent_for_power_builtin(
            inner_power.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )? && self.obj_is_verified_integer_exponent_for_power_builtin(
            nested_power.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !exponents_are_integer {
            return Ok(false);
        }
        self.obj_is_verified_nonzero_for_power_builtin(
            combined_power.base.as_ref(),
            line_file,
            verify_state,
        )
    }

    pub(crate) fn try_verify_power_of_power_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let holds = match (left, right) {
            (Obj::Pow(left_power), Obj::Pow(right_power)) => {
                self.power_of_power_rule_holds_one_direction(
                    left_power,
                    right_power,
                    line_file.clone(),
                    verify_state,
                )? || self.power_of_power_rule_holds_one_direction(
                    right_power,
                    left_power,
                    line_file.clone(),
                    verify_state,
                )?
            }
            _ => false,
        };
        if holds {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: (a^m)^n = a^(m*n) for natural exponents over real bases, positive exponents, or integer exponents with nonzero base",
            )));
        }
        Ok(None)
    }

    fn power_product_rule_holds_one_direction(
        &mut self,
        combined_power: &Pow,
        product: &Mul,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Mul(combined_base) = combined_power.base.as_ref() else {
            return Ok(false);
        };
        let exponent_in_n_pos = self.obj_is_verified_in_n_pos(
            combined_power.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !exponent_in_n_pos {
            let exponent_in_n = self.obj_is_verified_in_standard_set_for_power_builtin(
                combined_power.exponent.as_ref(),
                StandardSet::N,
                line_file.clone(),
                verify_state,
            )?;
            let natural_exponent_over_real_bases = if exponent_in_n {
                let left_base_in_r = self.obj_is_verified_in_standard_set_for_power_builtin(
                    combined_base.left.as_ref(),
                    StandardSet::R,
                    line_file.clone(),
                    verify_state,
                )?;
                let right_base_in_r = self.obj_is_verified_in_standard_set_for_power_builtin(
                    combined_base.right.as_ref(),
                    StandardSet::R,
                    line_file.clone(),
                    verify_state,
                )?;
                left_base_in_r && right_base_in_r
            } else {
                false
            };

            let integer_exponent_over_nonzero_bases = if natural_exponent_over_real_bases {
                false
            } else {
                let exponent_is_integer = self.obj_is_verified_integer_exponent_for_power_builtin(
                    combined_power.exponent.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !exponent_is_integer {
                    false
                } else {
                    let left_base_nonzero = self.obj_is_verified_nonzero_for_power_builtin(
                        combined_base.left.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?;
                    let right_base_nonzero = self.obj_is_verified_nonzero_for_power_builtin(
                        combined_base.right.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?;
                    let combined_base_nonzero = self.obj_is_verified_nonzero_for_power_builtin(
                        combined_power.base.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?;
                    left_base_nonzero && right_base_nonzero && combined_base_nonzero
                }
            };

            if !natural_exponent_over_real_bases && !integer_exponent_over_nonzero_bases {
                return Ok(false);
            }
        }

        // Product power law for natural integer exponents over real bases, and the
        // existing positive-integer exponent shape; integer exponents need nonzero
        // factors so negative powers are defined.
        // Example: `forall a,b R_nz, n Z: (a*b)^n = a^n*b^n`.
        let candidates = [
            (
                product.left.as_ref(),
                product.right.as_ref(),
                combined_base.left.as_ref(),
                combined_base.right.as_ref(),
            ),
            (
                product.right.as_ref(),
                product.left.as_ref(),
                combined_base.left.as_ref(),
                combined_base.right.as_ref(),
            ),
        ];

        for (left_factor, right_factor, left_base, right_base) in candidates {
            if !self.power_factor_matches_base_and_exponent(
                left_factor,
                left_base,
                combined_power.exponent.as_ref(),
                line_file.clone(),
                verify_state,
            )? {
                continue;
            }
            if !self.power_factor_matches_base_and_exponent(
                right_factor,
                right_base,
                combined_power.exponent.as_ref(),
                line_file.clone(),
                verify_state,
            )? {
                continue;
            }
            return Ok(true);
        }

        Ok(false)
    }

    pub(crate) fn try_verify_power_product_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let holds = match (left, right) {
            (Obj::Pow(pow), Obj::Mul(product)) => self.power_product_rule_holds_one_direction(
                pow,
                product,
                line_file.clone(),
                verify_state,
            )?,
            (Obj::Mul(product), Obj::Pow(pow)) => self.power_product_rule_holds_one_direction(
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
                "equality: (a*b)^n = a^n * b^n for n in N over real bases, n in N_pos, or n in Z with nonzero bases",
            )));
        }
        Ok(None)
    }

    pub(crate) fn try_verify_base_zero_from_known_positive_power_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let zero_obj = Self::literal_zero_obj_for_abs_builtin();
        let target_base = if Self::obj_is_builtin_literal_zero(left) {
            right
        } else if Self::obj_is_builtin_literal_zero(right) {
            left
        } else {
            return Ok(None);
        };

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
                let Obj::Pow(pow) = equal_obj else {
                    continue;
                };
                let base_result = self.verify_zero_product_factor_matches_target(
                    target_base,
                    pow.base.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !base_result.is_true() {
                    continue;
                }
                let exponent_result = self.obj_is_verified_in_n_pos(
                    pow.exponent.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !exponent_result {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: a = 0 from a^n = 0 and n in N_pos",
                )));
            }
        }

        Ok(None)
    }

    fn collect_known_equal_power_exponents_for_bases(
        &self,
        left_base: &Obj,
        right_base: &Obj,
    ) -> Vec<Obj> {
        let mut exponents = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for environment in self.iter_environments_from_top() {
            for (_, equal_objs) in environment.known_equality.values() {
                let mut left_exponents = Vec::new();
                let mut right_exponents = Vec::new();
                for obj in equal_objs.iter() {
                    let Obj::Pow(pow) = obj else {
                        continue;
                    };
                    if objs_equal_by_display_string(pow.base.as_ref(), left_base) {
                        left_exponents.push(pow.exponent.as_ref().clone());
                    }
                    if objs_equal_by_display_string(pow.base.as_ref(), right_base) {
                        right_exponents.push(pow.exponent.as_ref().clone());
                    }
                }
                for left_exponent in left_exponents.iter() {
                    for right_exponent in right_exponents.iter() {
                        if !objs_equal_by_display_string(left_exponent, right_exponent) {
                            continue;
                        }
                        let key = left_exponent.to_string();
                        if seen.insert(key) {
                            exponents.push(left_exponent.clone());
                        }
                    }
                }
            }
        }
        exponents
    }

    // Positive bases are injective under nonzero integer powers.
    // Example: from `0 < x`, `0 < y`, `n in Z`, `n != 0`, and `x^n = y^n`, prove `x = y`.
    pub(crate) fn try_verify_positive_base_equal_from_equal_nonzero_integer_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let zero = Self::literal_zero_obj_for_abs_builtin();
        let exponents = self.collect_known_equal_power_exponents_for_bases(left, right);
        for exponent in exponents {
            let left_positive: AtomicFact =
                LessFact::new(zero.clone(), left.clone(), line_file.clone()).into();
            let right_positive: AtomicFact =
                LessFact::new(zero.clone(), right.clone(), line_file.clone()).into();
            let exponent_in_z: AtomicFact =
                InFact::new(exponent.clone(), StandardSet::Z.into(), line_file.clone()).into();
            let exponent_nonzero: AtomicFact =
                NotEqualFact::new(exponent.clone(), zero.clone(), line_file.clone()).into();

            let left_positive_result = self.verify_non_equational_known_then_builtin_rules_only(
                &left_positive,
                verify_state,
            )?;
            if !left_positive_result.is_true() {
                continue;
            }
            let right_positive_result = self.verify_non_equational_known_then_builtin_rules_only(
                &right_positive,
                verify_state,
            )?;
            if !right_positive_result.is_true() {
                continue;
            }
            let exponent_in_z_result = self.verify_non_equational_known_then_builtin_rules_only(
                &exponent_in_z,
                verify_state,
            )?;
            if !exponent_in_z_result.is_true() {
                continue;
            }
            let exponent_nonzero_result = self
                .verify_non_equational_known_then_builtin_rules_only(
                    &exponent_nonzero,
                    verify_state,
                )?;
            if !exponent_nonzero_result.is_true() {
                continue;
            }

            let left_power: Obj = Pow::new(left.clone(), exponent.clone()).into();
            let right_power: Obj = Pow::new(right.clone(), exponent).into();
            let power_equal_result =
                self.verify_objs_are_equal_known_only(&left_power, &right_power, line_file.clone());
            if !power_equal_result.is_true() {
                continue;
            }

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: positive bases equal from equal nonzero integer powers",
                vec![
                    left_positive_result,
                    right_positive_result,
                    exponent_in_z_result,
                    exponent_nonzero_result,
                    power_equal_result,
                ],
            )));
        }
        Ok(None)
    }

    pub(crate) fn try_verify_abs_power_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (abs, pow) = match (left, right) {
            (Obj::Abs(abs), Obj::Pow(pow)) => (abs, pow),
            (Obj::Pow(pow), Obj::Abs(abs)) => (abs, pow),
            _ => return Ok(None),
        };
        let Obj::Pow(inner_pow) = abs.arg.as_ref() else {
            return Ok(None);
        };
        let Obj::Abs(abs_base) = pow.base.as_ref() else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                inner_pow.base.as_ref(),
                abs_base.arg.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                inner_pow.exponent.as_ref(),
                pow.exponent.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if self.obj_is_verified_in_n_pos(
            inner_pow.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: abs(a^n) = abs(a)^n for n in N_pos",
            )));
        }

        // Absolute value commutes with natural powers over real bases, including n = 0.
        // Example: `forall a R, n N: abs(a^n) = abs(a)^n`.
        let exponent_in_n = self.obj_is_verified_in_standard_set_for_power_builtin(
            inner_pow.exponent.as_ref(),
            StandardSet::N,
            line_file.clone(),
            verify_state,
        )?;
        let base_in_r = self.obj_is_verified_in_standard_set_for_power_builtin(
            inner_pow.base.as_ref(),
            StandardSet::R,
            line_file.clone(),
            verify_state,
        )?;
        if exponent_in_n && base_in_r {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: abs(a^n) = abs(a)^n for n in N over real bases",
            )));
        }

        // Integer powers of a nonzero base preserve the absolute-value power law.
        // Example: `forall a R_nz, n Z: abs(a^n) = abs(a)^n`.
        if !self.obj_is_verified_integer_exponent_for_power_builtin(
            inner_pow.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }
        if !self.obj_is_verified_nonzero_for_power_builtin(
            inner_pow.base.as_ref(),
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: abs(a^n) = abs(a)^n for n in Z and a != 0",
        )))
    }

    fn positive_exponent_from_negated_power_exponent(exponent: &Obj) -> Option<Obj> {
        match exponent {
            Obj::Mul(mul) if Self::obj_is_builtin_literal_neg_one(mul.left.as_ref()) => {
                Some(mul.right.as_ref().clone())
            }
            Obj::Mul(mul) if Self::obj_is_builtin_literal_neg_one(mul.right.as_ref()) => {
                Some(mul.left.as_ref().clone())
            }
            Obj::Sub(sub) if Self::obj_is_builtin_literal_zero(sub.left.as_ref()) => {
                Some(sub.right.as_ref().clone())
            }
            _ => None,
        }
    }

    fn power_inverse_rule_holds_one_direction(
        &mut self,
        negative_power: &Pow,
        quotient: &Div,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        if !Self::obj_is_builtin_literal_one(quotient.left.as_ref()) {
            return Ok(None);
        }
        let Obj::Pow(denominator_power) = quotient.right.as_ref() else {
            return Ok(None);
        };
        let Some(positive_exponent) =
            Self::positive_exponent_from_negated_power_exponent(negative_power.exponent.as_ref())
        else {
            return Ok(None);
        };
        let positive_exponent_for_display = positive_exponent.clone();

        let base_result = self.verify_objs_are_equal_in_equality_builtin(
            negative_power.base.as_ref(),
            denominator_power.base.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !base_result.is_true() {
            return Ok(None);
        }

        let exponent_result = self.verify_objs_are_equal_in_equality_builtin(
            &positive_exponent,
            denominator_power.exponent.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !exponent_result.is_true() {
            return Ok(None);
        }

        let exponent_in_n_pos: AtomicFact = InFact::new(
            positive_exponent,
            StandardSet::NPos.into(),
            line_file.clone(),
        )
        .into();
        let exponent_in_n_pos_result = self.verify_non_equational_known_then_builtin_rules_only(
            &exponent_in_n_pos,
            verify_state,
        )?;
        if !exponent_in_n_pos_result.is_true() {
            return Ok(None);
        }

        let denominator_nonzero: AtomicFact = NotEqualFact::new(
            quotient.right.as_ref().clone(),
            Self::literal_zero_obj_for_abs_builtin(),
            line_file,
        )
        .into();
        let denominator_nonzero_result = self.verify_non_equational_known_then_builtin_rules_only(
            &denominator_nonzero,
            verify_state,
        )?;
        if !denominator_nonzero_result.is_true() {
            return Ok(None);
        }

        let mut subgoals = Vec::new();
        if !objs_equal_by_display_string(
            negative_power.base.as_ref(),
            denominator_power.base.as_ref(),
        ) {
            subgoals.push(base_result);
        }
        if !objs_equal_by_display_string(
            &positive_exponent_for_display,
            denominator_power.exponent.as_ref(),
        ) {
            subgoals.push(exponent_result);
        }
        subgoals.push(exponent_in_n_pos_result);
        subgoals.push(denominator_nonzero_result);
        Ok(Some(subgoals))
    }

    // Negative integer powers are reciprocals of the corresponding positive powers.
    // Example: for `x != 0` and `n in N_pos`, prove `x^(-n) = 1 / x^n`.
    pub(crate) fn try_verify_power_inverse_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let subgoals = match (left, right) {
            (Obj::Pow(negative_power), Obj::Div(quotient)) => self
                .power_inverse_rule_holds_one_direction(
                    negative_power,
                    quotient,
                    line_file.clone(),
                    verify_state,
                )?,
            (Obj::Div(quotient), Obj::Pow(negative_power)) => self
                .power_inverse_rule_holds_one_direction(
                    negative_power,
                    quotient,
                    line_file.clone(),
                    verify_state,
                )?,
            _ => None,
        };
        let Some(subgoals) = subgoals else {
            return Ok(None);
        };
        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            left,
            right,
            line_file,
            "equality: a^(-n) = 1 / a^n for n in N_pos and a^n != 0",
            subgoals,
        )))
    }

    fn reciprocal_positive_integer_denominator_for_power_root_builtin(
        exponent: &Obj,
    ) -> Option<Obj> {
        let Obj::Div(div) = exponent else {
            return None;
        };
        if !Self::obj_is_builtin_literal_one(div.left.as_ref()) {
            return None;
        }
        Some(div.right.as_ref().clone())
    }

    // Principal nth-root equality: `x^(1/n) = z` follows from `x = z^n`,
    // with `n` a positive integer and `z >= 0`.
    // Example: `8^(1/3) = 2`, since `3 $in N_pos`, `0 <= 2`, and `8 = 2^3`.
    pub(crate) fn try_verify_pow_reciprocal_exponent_equals_root_by_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (pow, root) = match (left, right) {
            (Obj::Pow(pow), root) => (pow, root),
            (root, Obj::Pow(pow)) => (pow, root),
            _ => return Ok(None),
        };
        let Some(degree) = Self::reciprocal_positive_integer_denominator_for_power_root_builtin(
            pow.exponent.as_ref(),
        ) else {
            return Ok(None);
        };

        let degree_in_n_pos: AtomicFact =
            InFact::new(degree.clone(), StandardSet::NPos.into(), line_file.clone()).into();
        let degree_result = self
            .verify_non_equational_known_then_builtin_rules_only(&degree_in_n_pos, verify_state)?;
        if !degree_result.is_true() {
            return Ok(None);
        }

        let root_nonnegative: AtomicFact = LessEqualFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            root.clone(),
            line_file.clone(),
        )
        .into();
        let root_nonnegative_result = self
            .verify_non_equational_known_then_builtin_rules_only(&root_nonnegative, verify_state)?;
        if !root_nonnegative_result.is_true() {
            return Ok(None);
        }

        let root_power: Obj = Pow::new(root.clone(), degree).into();
        let inverse_result = self.verify_objs_are_equal_in_equality_builtin(
            pow.base.as_ref(),
            &root_power,
            line_file.clone(),
            verify_state,
        )?;
        if !inverse_result.is_true() {
            return Ok(None);
        }

        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            left,
            right,
            line_file,
            "equality: x^(1/n) = z from x = z^n, n in N_pos, and z >= 0",
            vec![degree_result, root_nonnegative_result, inverse_result],
        )))
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
                    let mut subgoals = equality_builtin_match_subgoals(
                        p.base.as_ref(),
                        log.base.as_ref(),
                        base_ok,
                    );
                    subgoals.extend(equality_builtin_match_subgoals(
                        p.exponent.as_ref(),
                        other,
                        exp_ok,
                    ));
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        left,
                        right,
                        line_file,
                        "equality: log(a, a^b) = b",
                        subgoals,
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
            let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: log(a^b, c) = log(a, c) / b",
                subgoals,
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
                let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x^b) = b * log(a, x)",
                    subgoals,
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
                let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x*y) = log(a, x) + log(a, y)",
                    subgoals,
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
            let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: log(a, x/y) = log(a, x) - log(a, y)",
                subgoals,
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
                let mut subgoals = equality_builtin_match_subgoals(d.left.as_ref(), &one, one_ok);
                subgoals.extend(equality_builtin_match_subgoals(other, &expected, ok));
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: log(a, 1/x) = -log(a, x)",
                    subgoals,
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

        let mut subgoals =
            equality_builtin_match_subgoals(log_cb.base.as_ref(), log_ca.base.as_ref(), base_ok);
        subgoals.extend(equality_builtin_match_subgoals(
            log_cb.arg.as_ref(),
            log_ab.arg.as_ref(),
            arg_ok,
        ));
        subgoals.extend(equality_builtin_match_subgoals(
            log_ca.arg.as_ref(),
            log_ab.base.as_ref(),
            inner_ok,
        ));

        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            left,
            right,
            line_file,
            "equality: log(a, b) = log(c, b) / log(c, a)",
            subgoals,
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
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: log(a, b) = c from a^c = b",
                vec![inner],
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

        let then_fact: AtomicFact =
            EqualFact::new(l_inst, Add::new(a_inst, b_inst).into(), line_file.clone()).into();

        let dom_lo: Fact =
            LessEqualFact::new((*sum_m.start).clone(), x_obj.clone(), line_file.clone()).into();
        let dom_hi: Fact =
            LessEqualFact::new(x_obj.clone(), (*sum_m.end).clone(), line_file.clone()).into();

        let r = self.verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            vec![dom_lo, dom_hi],
            &then_fact,
            verify_state,
        )?;
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

    pub(crate) fn instantiate_unary_anonymous_summand_at(
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

    pub(crate) fn verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
        &mut self,
        param_name: String,
        dom_facts: Vec<Fact>,
        then_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![param_name],
                ParamType::Obj(StandardSet::Z.into()),
            )]);
            rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
            for dom_fact in dom_facts {
                rt.store_fact_without_forall_coverage_check_and_infer(dom_fact)?;
            }
            rt.verify_atomic_fact_by_known_atomic_or_builtin_only(then_fact, verify_state)
        })
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
            let then_fact: AtomicFact = EqualFact::new(at_l, at_r, line_file.clone()).into();
            let dom_lo: Fact =
                LessEqualFact::new((*r_sum.start).clone(), y_obj.clone(), line_file.clone()).into();
            let dom_hi: Fact =
                LessEqualFact::new(y_obj.clone(), (*r_sum.end).clone(), line_file.clone()).into();
            let r = self.verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                y_name,
                vec![dom_lo, dom_hi],
                &then_fact,
                verify_state,
            )?;
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

    // Scalars factor out of finite sums over the same integer index range.
    // Example: `sum(m, n, '(i Z) R {c * a(i)}) = c * sum(m, n, '(i Z) R {a(i)})`.
    pub(crate) fn try_verify_sum_scalar_mul(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }

        for (sum_side, product_side) in [(left, right), (right, left)] {
            let Obj::Sum(sum) = sum_side else {
                continue;
            };
            let Obj::Mul(product) = product_side else {
                continue;
            };
            for (base_side, scalar) in [
                (product.left.as_ref(), product.right.as_ref()),
                (product.right.as_ref(), product.left.as_ref()),
            ] {
                let Obj::Sum(base_sum) = base_side else {
                    continue;
                };
                let start_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.start.as_ref(),
                    base_sum.start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !start_result.is_true() {
                    continue;
                }
                let end_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.end.as_ref(),
                    base_sum.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !end_result.is_true() {
                    continue;
                }

                let x_name = self.generate_random_unused_name();
                let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
                let Some(sum_inst) =
                    self.instantiate_unary_anonymous_summand_at(sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let Some(base_inst) =
                    self.instantiate_unary_anonymous_summand_at(base_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let expected: Obj = Mul::new(scalar.clone(), base_inst).into();
                let pointwise_fact: AtomicFact =
                    EqualFact::new(sum_inst, expected, line_file.clone()).into();
                let dom_lo: Fact =
                    LessEqualFact::new((*sum.start).clone(), x_obj.clone(), line_file.clone())
                        .into();
                let dom_hi: Fact =
                    LessEqualFact::new(x_obj.clone(), (*sum.end).clone(), line_file.clone()).into();
                let pointwise_result = self
                    .verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                        x_name,
                        vec![dom_lo, dom_hi],
                        &pointwise_fact,
                        verify_state,
                    )?;
                if !pointwise_result.is_true() {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite sum scalar multiplication",
                )));
            }
        }
        Ok(None)
    }

    // A finite-set sum over the empty set is zero.
    // Example: `finite_set_sum({}, 'Z(x){x}) = 0`.
    pub(crate) fn try_verify_finite_set_sum_empty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let empty_set: Obj = ListSet::new(vec![]).into();
        let zero: Obj = Number::new("0".to_string()).into();
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(s) = sum_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s.set.as_ref(),
                    &empty_set,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &zero,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum over empty set is zero",
                )));
            }
        }
        Ok(None)
    }

    // A finite-set sum over a displayed finite set expands to the left-associated sum
    // of the summand at each listed element. Example:
    // `finite_set_sum({1, 2}, 'Z(x){x}) = 1 + 2`.
    pub(crate) fn try_verify_finite_set_sum_list_expansion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(s) = sum_side else {
                continue;
            };
            let Obj::ListSet(list_set) = s.set.as_ref() else {
                continue;
            };
            let mut terms = Vec::with_capacity(list_set.list.len());
            for element in list_set.list.iter() {
                let Some(term) =
                    self.instantiate_unary_function_at(s.func.as_ref(), element.as_ref())?
                else {
                    terms.clear();
                    break;
                };
                terms.push(term);
            }
            if terms.len() != list_set.list.len() {
                continue;
            }
            let expected = Self::left_assoc_add_from_terms(terms);
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &expected,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum over displayed set expands elementwise",
                )));
            }
        }
        Ok(None)
    }

    // A finite-set sum over an integer closed range agrees with the existing range sum.
    // Example: `finite_set_sum(1...3, 'Z(x){x}) = sum(1, 3, 'Z(x){x})`.
    pub(crate) fn try_verify_finite_set_sum_closed_range_bridge(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (finite_side, range_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(finite_sum) = finite_side else {
                continue;
            };
            let Obj::ClosedRange(range) = finite_sum.set.as_ref() else {
                continue;
            };
            let Obj::Sum(range_sum) = range_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    range.start.as_ref(),
                    range_sum.start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    range.end.as_ref(),
                    range_sum.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let exact_func_result = self.verify_objs_are_equal_in_equality_builtin(
                finite_sum.func.as_ref(),
                range_sum.func.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !exact_func_result.is_true() {
                let x_name = self.generate_random_unused_name();
                let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
                let Some(finite_inst) =
                    self.instantiate_unary_function_at(finite_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let Some(range_inst) =
                    self.instantiate_unary_function_at(range_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let pointwise_fact: AtomicFact =
                    EqualFact::new(finite_inst, range_inst, line_file.clone()).into();
                let dom_lo: Fact = LessEqualFact::new(
                    (*range_sum.start).clone(),
                    x_obj.clone(),
                    line_file.clone(),
                )
                .into();
                let dom_hi: Fact =
                    LessEqualFact::new(x_obj, (*range_sum.end).clone(), line_file.clone()).into();
                let pointwise_result = self
                    .verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                        x_name,
                        vec![dom_lo, dom_hi],
                        &pointwise_fact,
                        verify_state,
                    )?;
                if !pointwise_result.is_true() {
                    continue;
                }
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sum over closed integer range equals range sum",
            )));
        }
        Ok(None)
    }

    // A constant finite-set summand is the set cardinality times the constant.
    // Example: `finite_set_sum(X, '(x X) R {c}) = count(X) * c`.
    pub(crate) fn try_verify_finite_set_sum_constant_summand(
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
            let Obj::SumOfFiniteSet(s) = sum_side else {
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
            let count: Obj = Count::new((*s.set).clone()).into();
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
                    "equality: finite-set sum of a constant summand",
                )));
            }
        }
        Ok(None)
    }

    // Finite-set sums are equal when their summands are pointwise equal on the same finite set.
    // Example: from `forall x X: f(x) = g(x)`, prove
    // `finite_set_sum(X, f) = finite_set_sum(X, g)`.
    pub(crate) fn try_verify_finite_set_sum_pointwise_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (left_sum, right_sum) = match (left, right) {
            (Obj::SumOfFiniteSet(l), Obj::SumOfFiniteSet(r)) => (l, r),
            _ => return Ok(None),
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_sum.set.as_ref(),
                right_sum.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let Some(left_inst) = self.instantiate_unary_function_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_function_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let then_fact: AtomicFact = EqualFact::new(left_inst, right_inst, line_file.clone()).into();
        let r = self.verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            left_sum.set.as_ref().clone(),
            &then_fact,
            verify_state,
        )?;
        if r.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sums from pointwise equality on the finite set",
            )));
        }
        Ok(None)
    }

    // Finite-set sum substitution along a bijection onto the original set.
    // Example: from `forall x X: exist! y Y st {g(y) = x}`, prove
    // `finite_set_sum(X, f) = finite_set_sum(Y, '(y Y) R {f(g(y))})`.
    pub(crate) fn try_verify_finite_set_sum_substitution(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (source_side, pullback_side) in [(left, right), (right, left)] {
            let (Obj::SumOfFiniteSet(source_sum), Obj::SumOfFiniteSet(pullback_sum)) =
                (source_side, pullback_side)
            else {
                continue;
            };

            let y_name = self.generate_random_unused_name();
            let y_obj = obj_for_bound_param_in_scope(y_name.clone(), ParamObjType::Forall);
            let Some(pullback_at_y) =
                self.instantiate_unary_function_at(pullback_sum.func.as_ref(), &y_obj)?
            else {
                continue;
            };
            let Some(map_y) = Self::unary_application_arg_matching_callable(
                &pullback_at_y,
                source_sum.func.as_ref(),
            ) else {
                continue;
            };
            let Some(source_at_map_y) =
                self.instantiate_unary_function_at(source_sum.func.as_ref(), &map_y)?
            else {
                continue;
            };
            let pointwise_fact: AtomicFact =
                EqualFact::new(pullback_at_y, source_at_map_y, line_file.clone()).into();
            let pointwise_result = self
                .verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                    y_name,
                    pullback_sum.set.as_ref().clone(),
                    &pointwise_fact,
                    verify_state,
                )?;
            if !pointwise_result.is_true() {
                continue;
            }

            let base_name = self.generate_random_unused_name();
            let x_name = format!("{}a", base_name);
            let exist_y_name = format!("{}b", base_name);
            let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
            let exist_y_obj =
                obj_for_bound_param_in_scope(exist_y_name.clone(), ParamObjType::Exist);
            let Some(pullback_at_exist_y) =
                self.instantiate_unary_function_at(pullback_sum.func.as_ref(), &exist_y_obj)?
            else {
                continue;
            };
            let Some(map_exist_y) = Self::unary_application_arg_matching_callable(
                &pullback_at_exist_y,
                source_sum.func.as_ref(),
            ) else {
                continue;
            };
            let preimage_eq: AtomicFact =
                EqualFact::new(map_exist_y, x_obj, line_file.clone()).into();
            let exist_body = ExistFactBody::new(
                ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![exist_y_name],
                    ParamType::Obj(pullback_sum.set.as_ref().clone()),
                )]),
                vec![ExistBodyFact::AtomicFact(preimage_eq)],
                line_file.clone(),
            )?;
            let unique_preimage_fact: Fact = ExistFactEnum::ExistUniqueFact(exist_body).into();
            let unique_preimage_result = self.run_in_local_env(|rt| {
                let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![x_name],
                    ParamType::Obj(source_sum.set.as_ref().clone()),
                )]);
                rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
                rt.verify_fact_full(&unique_preimage_fact, verify_state)
            })?;
            if !unique_preimage_result.is_true() {
                continue;
            }

            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sum substitution along a uniquely-covered index set",
            )));
        }
        Ok(None)
    }

    // Finite-set sums split over disjoint unions.
    // Example: from `intersect(X, Y) = {}`, prove
    // `finite_set_sum(union(X, Y), f) = finite_set_sum(X, f|X) + finite_set_sum(Y, f|Y)`.
    pub(crate) fn try_verify_finite_set_sum_disjoint_union(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (union_side, add_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(union_sum) = union_side else {
                continue;
            };
            let Obj::Add(add) = add_side else {
                continue;
            };
            for (first_side, second_side) in [
                (add.left.as_ref(), add.right.as_ref()),
                (add.right.as_ref(), add.left.as_ref()),
            ] {
                let (Obj::SumOfFiniteSet(first_sum), Obj::SumOfFiniteSet(second_sum)) =
                    (first_side, second_side)
                else {
                    continue;
                };
                let expected_union: Obj = Union::new(
                    first_sum.set.as_ref().clone(),
                    second_sum.set.as_ref().clone(),
                )
                .into();
                let union_result = self.verify_objs_are_equal_in_equality_builtin(
                    union_sum.set.as_ref(),
                    &expected_union,
                    line_file.clone(),
                    verify_state,
                )?;
                if !union_result.is_true() {
                    continue;
                }
                let empty_set: Obj = ListSet::new(vec![]).into();
                let intersection: Obj = Intersect::new(
                    first_sum.set.as_ref().clone(),
                    second_sum.set.as_ref().clone(),
                )
                .into();
                let disjoint_result = self.verify_objs_are_equal_in_equality_builtin(
                    &intersection,
                    &empty_set,
                    line_file.clone(),
                    verify_state,
                )?;
                if !disjoint_result.is_true() {
                    continue;
                }
                let first_pointwise = self.verify_finite_set_sum_functions_pointwise_equal(
                    union_sum.func.as_ref(),
                    first_sum.func.as_ref(),
                    first_sum.set.as_ref().clone(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !first_pointwise.is_true() {
                    continue;
                }
                let second_pointwise = self.verify_finite_set_sum_functions_pointwise_equal(
                    union_sum.func.as_ref(),
                    second_sum.func.as_ref(),
                    second_sum.set.as_ref().clone(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !second_pointwise.is_true() {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum over a disjoint union",
                )));
            }
        }
        Ok(None)
    }

    // Finite-set sums distribute over pointwise addition on the same finite set.
    // Example: `finite_set_sum(X, '(x X) R {f(x) + g(x)}) =
    // finite_set_sum(X, f) + finite_set_sum(X, g)`.
    pub(crate) fn try_verify_finite_set_sum_add(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (sum_side, add_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(sum) = sum_side else {
                continue;
            };
            let Obj::Add(add) = add_side else {
                continue;
            };
            let (Obj::SumOfFiniteSet(first_sum), Obj::SumOfFiniteSet(second_sum)) =
                (add.left.as_ref(), add.right.as_ref())
            else {
                continue;
            };
            let first_set_result = self.verify_objs_are_equal_in_equality_builtin(
                sum.set.as_ref(),
                first_sum.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !first_set_result.is_true() {
                continue;
            }
            let second_set_result = self.verify_objs_are_equal_in_equality_builtin(
                sum.set.as_ref(),
                second_sum.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !second_set_result.is_true() {
                continue;
            }

            let x_name = self.generate_random_unused_name();
            let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
            let Some(sum_inst) = self.instantiate_unary_function_at(sum.func.as_ref(), &x_obj)?
            else {
                continue;
            };
            let Some(first_inst) =
                self.instantiate_unary_function_at(first_sum.func.as_ref(), &x_obj)?
            else {
                continue;
            };
            let Some(second_inst) =
                self.instantiate_unary_function_at(second_sum.func.as_ref(), &x_obj)?
            else {
                continue;
            };
            let expected: Obj = Add::new(first_inst, second_inst).into();
            let pointwise_fact: AtomicFact =
                EqualFact::new(sum_inst, expected, line_file.clone()).into();
            let pointwise_result = self
                .verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                    x_name,
                    sum.set.as_ref().clone(),
                    &pointwise_fact,
                    verify_state,
                )?;
            if !pointwise_result.is_true() {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sum distributes over pointwise addition",
            )));
        }
        Ok(None)
    }

    // Scalars factor out of finite-set sums on the same finite set.
    // Example: `finite_set_sum(X, '(x X) R {c * f(x)}) = c * finite_set_sum(X, f)`.
    pub(crate) fn try_verify_finite_set_sum_scalar_mul(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (sum_side, product_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(sum) = sum_side else {
                continue;
            };
            let Obj::Mul(product) = product_side else {
                continue;
            };
            for (base_side, scalar) in [
                (product.left.as_ref(), product.right.as_ref()),
                (product.right.as_ref(), product.left.as_ref()),
            ] {
                let Obj::SumOfFiniteSet(base_sum) = base_side else {
                    continue;
                };
                let set_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.set.as_ref(),
                    base_sum.set.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !set_result.is_true() {
                    continue;
                }

                let x_name = self.generate_random_unused_name();
                let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
                let Some(sum_inst) =
                    self.instantiate_unary_function_at(sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let Some(base_inst) =
                    self.instantiate_unary_function_at(base_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let expected: Obj = Mul::new(scalar.clone(), base_inst).into();
                let pointwise_fact: AtomicFact =
                    EqualFact::new(sum_inst, expected, line_file.clone()).into();
                let pointwise_result = self
                    .verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                        x_name,
                        sum.set.as_ref().clone(),
                        &pointwise_fact,
                        verify_state,
                    )?;
                if !pointwise_result.is_true() {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum scalar multiplication",
                )));
            }
        }
        Ok(None)
    }

    // A nested finite-set sum over two finite sets is the finite-set sum over
    // their Cartesian product.
    // Example: `finite_set_sum(X, '(x X) R {finite_set_sum(Y, '(y Y) R {f((x, y))})})
    // = finite_set_sum(cart(X, Y), f)`.
    pub(crate) fn try_verify_finite_set_sum_over_cartesian_product(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (nested_side, flat_side) in [(left, right), (right, left)] {
            let Some(nested_shape) = self.nested_finite_set_sum_cartesian_shape(
                nested_side,
                line_file.clone(),
                verify_state,
            )?
            else {
                continue;
            };
            let Obj::SumOfFiniteSet(flat_sum) = flat_side else {
                continue;
            };
            let set_result = self.verify_objs_are_equal_in_equality_builtin(
                flat_sum.set.as_ref(),
                &nested_shape.product_set,
                line_file.clone(),
                verify_state,
            )?;
            if !set_result.is_true() {
                continue;
            }
            let func_result = self.verify_objs_are_equal_in_equality_builtin(
                flat_sum.func.as_ref(),
                &nested_shape.function,
                line_file.clone(),
                verify_state,
            )?;
            if !func_result.is_true() {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: double finite-set sum over Cartesian product",
            )));
        }
        Ok(None)
    }

    // Fubini for finite-set sums: two nested sums with the same flattened
    // Cartesian-product summand can swap their summation order.
    // Example: `sum_X sum_Y f((x, y)) = sum_Y sum_X f((x, y))`.
    pub(crate) fn try_verify_finite_set_sum_fubini(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let Some(left_shape) =
            self.nested_finite_set_sum_cartesian_shape(left, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };
        let Some(right_shape) =
            self.nested_finite_set_sum_cartesian_shape(right, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };
        let set_result = self.verify_objs_are_equal_in_equality_builtin(
            &left_shape.product_set,
            &right_shape.product_set,
            line_file.clone(),
            verify_state,
        )?;
        if !set_result.is_true() {
            return Ok(None);
        }
        let func_result = self.verify_objs_are_equal_in_equality_builtin(
            &left_shape.function,
            &right_shape.function,
            line_file.clone(),
            verify_state,
        )?;
        if !func_result.is_true() {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: finite-set Fubini over Cartesian product",
        )))
    }

    // Range sums over two bijective enumerations of the same finite set are equal.
    // Example: from `forall x X: exist! i 1...count(X) st {g(i) = x}` and the
    // analogous fact for `h`, prove `sum(1, count(X), '(i 1...count(X)) R {f(g(i))})
    // = sum(1, count(X), '(i 1...count(X)) R {f(h(i))})`.
    pub(crate) fn try_verify_sum_over_bijective_finite_set_enumerations(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (left_sum, right_sum) = match (left, right) {
            (Obj::Sum(l), Obj::Sum(r)) => (l, r),
            _ => return Ok(None),
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_sum.start.as_ref(),
                right_sum.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_sum.end.as_ref(),
                right_sum.end.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        let Some(left_shape) =
            self.finite_set_enumeration_summand_shape(left_sum, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };
        let Some(right_shape) =
            self.finite_set_enumeration_summand_shape(right_sum, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };

        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &left_shape.outer_function,
                &right_shape.outer_function,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &left_shape.index_set,
                &right_shape.index_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &left_shape.target_set,
                &right_shape.target_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        let finite_target: AtomicFact =
            IsFiniteSetFact::new(left_shape.target_set.clone(), line_file.clone()).into();
        if !self
            .verify_non_equational_known_then_builtin_rules_only(&finite_target, verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        if !self.verify_unique_preimage_enumerator_fact(
            &left_shape,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }
        if !self.verify_unique_preimage_enumerator_fact(
            &right_shape,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }

        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: sums over bijective enumerations of the same finite set",
        )))
    }

    // A finite-set product over the empty set is one.
    // Example: `finite_set_product({}, 'Z(x){x}) = 1`.
    pub(crate) fn try_verify_finite_set_product_empty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let empty_set: Obj = ListSet::new(vec![]).into();
        let one: Obj = Number::new("1".to_string()).into();
        for (product_side, other) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(p) = product_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p.set.as_ref(),
                    &empty_set,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &one,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set product over empty set is one",
                )));
            }
        }
        Ok(None)
    }

    // A finite-set product over a displayed finite set expands to the left-associated product
    // of the factor at each listed element. Example:
    // `finite_set_product({1, 2}, 'Z(x){x}) = 1 * 2`.
    pub(crate) fn try_verify_finite_set_product_list_expansion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (product_side, other) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(p) = product_side else {
                continue;
            };
            let Obj::ListSet(list_set) = p.set.as_ref() else {
                continue;
            };
            let mut terms = Vec::with_capacity(list_set.list.len());
            for element in list_set.list.iter() {
                let Some(term) =
                    self.instantiate_unary_function_at(p.func.as_ref(), element.as_ref())?
                else {
                    terms.clear();
                    break;
                };
                terms.push(term);
            }
            if terms.len() != list_set.list.len() {
                continue;
            }
            let expected = Self::left_assoc_mul_from_terms(terms);
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &expected,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set product over displayed set expands elementwise",
                )));
            }
        }
        Ok(None)
    }

    // A finite-set product over an integer closed range agrees with the existing range product.
    // Example: `finite_set_product(1...3, 'Z(x){x}) = product(1, 3, 'Z(x){x})`.
    pub(crate) fn try_verify_finite_set_product_closed_range_bridge(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (finite_side, range_side) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(finite_product) = finite_side else {
                continue;
            };
            let Obj::ClosedRange(range) = finite_product.set.as_ref() else {
                continue;
            };
            let Obj::Product(range_product) = range_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    range.start.as_ref(),
                    range_product.start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    range.end.as_ref(),
                    range_product.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    finite_product.func.as_ref(),
                    range_product.func.as_ref(),
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
                "equality: finite-set product over closed integer range equals range product",
            )));
        }
        Ok(None)
    }

    // A constant finite-set factor is the constant raised to the set cardinality.
    // Example: `finite_set_product(X, '(x X) R {c}) = c ^ count(X)`.
    pub(crate) fn try_verify_finite_set_product_constant_factor(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (product_side, other) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(p) = product_side else {
                continue;
            };
            let af = match p.func.as_ref() {
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
            let count: Obj = Count::new((*p.set).clone()).into();
            let expected: Obj = Pow::new(c, count).into();
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &expected,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set product of a constant factor",
                )));
            }
        }
        Ok(None)
    }

    // Finite-set products are equal when their factors are pointwise equal on the same finite set.
    // Example: from `forall x X: f(x) = g(x)`, prove
    // `finite_set_product(X, f) = finite_set_product(X, g)`.
    pub(crate) fn try_verify_finite_set_product_pointwise_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (left_product, right_product) = match (left, right) {
            (Obj::ProductOfFiniteSet(l), Obj::ProductOfFiniteSet(r)) => (l, r),
            _ => return Ok(None),
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_product.set.as_ref(),
                right_product.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let Some(left_inst) =
            self.instantiate_unary_function_at(left_product.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_function_at(right_product.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let then_fact: AtomicFact = EqualFact::new(left_inst, right_inst, line_file.clone()).into();
        let r = self.verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            left_product.set.as_ref().clone(),
            &then_fact,
            verify_state,
        )?;
        if r.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set products from pointwise equality on the finite set",
            )));
        }
        Ok(None)
    }

    fn left_assoc_add_from_terms(terms: Vec<Obj>) -> Obj {
        let mut it = terms.into_iter();
        let Some(first) = it.next() else {
            return Number::new("0".to_string()).into();
        };
        let mut acc = first;
        for term in it {
            acc = Add::new(acc, term).into();
        }
        acc
    }

    fn left_assoc_mul_from_terms(terms: Vec<Obj>) -> Obj {
        let mut it = terms.into_iter();
        let Some(first) = it.next() else {
            return Number::new("1".to_string()).into();
        };
        let mut acc = first;
        for term in it {
            acc = Mul::new(acc, term).into();
        }
        acc
    }

    fn unary_application_arg_matching_callable(application: &Obj, callable: &Obj) -> Option<Obj> {
        let Obj::FnObj(fn_obj) = application else {
            return None;
        };
        if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
            return None;
        }
        let expected_head = FnObjHead::from_callable_obj(callable.clone())?;
        let actual_head_obj: Obj = fn_obj.head.as_ref().clone().into();
        let expected_head_obj: Obj = expected_head.into();
        if !objs_equal_by_display_string(&actual_head_obj, &expected_head_obj) {
            return None;
        }
        Some(fn_obj.body[0][0].as_ref().clone())
    }

    fn verify_finite_set_sum_functions_pointwise_equal(
        &mut self,
        left_func: &Obj,
        right_func: &Obj,
        set: Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let Some(left_inst) = self.instantiate_unary_function_at(left_func, &x_obj)? else {
            return Ok(StmtResult::Unknown(StmtUnknown::new()));
        };
        let Some(right_inst) = self.instantiate_unary_function_at(right_func, &x_obj)? else {
            return Ok(StmtResult::Unknown(StmtUnknown::new()));
        };
        let pointwise_fact: AtomicFact = EqualFact::new(left_inst, right_inst, line_file).into();
        self.verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            set,
            &pointwise_fact,
            verify_state,
        )
    }

    fn nested_finite_set_sum_cartesian_shape(
        &mut self,
        obj: &Obj,
        _line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<Option<NestedFiniteSetSumCartesianShape>, RuntimeError> {
        let Obj::SumOfFiniteSet(outer_sum) = obj else {
            return Ok(None);
        };
        let outer_name = self.generate_random_unused_name();
        let outer_obj = obj_for_bound_param_in_scope(outer_name.clone(), ParamObjType::Forall);
        let Some(inner_sum_obj) =
            self.instantiate_unary_function_at(outer_sum.func.as_ref(), &outer_obj)?
        else {
            return Ok(None);
        };
        let Obj::SumOfFiniteSet(inner_sum) = inner_sum_obj else {
            return Ok(None);
        };
        if obj_expr_mentions_bare_id(inner_sum.set.as_ref(), outer_name.as_str()) {
            return Ok(None);
        }

        let inner_name = format!("{}_inner", outer_name);
        let inner_obj = obj_for_bound_param_in_scope(inner_name.clone(), ParamObjType::Forall);
        let Some(summand) =
            self.instantiate_unary_function_at(inner_sum.func.as_ref(), &inner_obj)?
        else {
            return Ok(None);
        };
        let Obj::FnObj(call) = summand else {
            return Ok(None);
        };
        if call.body.len() != 1 || call.body[0].len() != 1 {
            return Ok(None);
        }
        let Obj::Tuple(tuple) = call.body[0][0].as_ref() else {
            return Ok(None);
        };
        if tuple.args.len() != 2 {
            return Ok(None);
        }

        let first_arg = tuple.args[0].as_ref();
        let second_arg = tuple.args[1].as_ref();
        let first_is_outer = verify_equality_by_they_are_the_same(first_arg, &outer_obj);
        let second_is_inner = verify_equality_by_they_are_the_same(second_arg, &inner_obj);
        let first_is_inner = verify_equality_by_they_are_the_same(first_arg, &inner_obj);
        let second_is_outer = verify_equality_by_they_are_the_same(second_arg, &outer_obj);
        let product_set: Obj = if first_is_outer && second_is_inner {
            Cart::new(vec![
                outer_sum.set.as_ref().clone(),
                inner_sum.set.as_ref().clone(),
            ])
            .into()
        } else if first_is_inner && second_is_outer {
            Cart::new(vec![
                inner_sum.set.as_ref().clone(),
                outer_sum.set.as_ref().clone(),
            ])
            .into()
        } else {
            return Ok(None);
        };
        let function: Obj = call.head.as_ref().clone().into();
        Ok(Some(NestedFiniteSetSumCartesianShape {
            product_set,
            function,
        }))
    }

    pub(crate) fn instantiate_unary_function_at(
        &mut self,
        func: &Obj,
        x: &Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        if let Some(instantiated) = self.instantiate_unary_anonymous_summand_at(func, x)? {
            return Ok(Some(instantiated));
        }
        if let Obj::FnObj(fo) = func {
            if !fo.body.is_empty() {
                return Ok(None);
            }
            return Ok(Some(
                FnObj::new((*fo.head).clone(), vec![vec![Box::new(x.clone())]]).into(),
            ));
        }
        let Some(head) = FnObjHead::from_callable_obj(func.clone()) else {
            return Ok(None);
        };
        Ok(Some(
            FnObj::new(head, vec![vec![Box::new(x.clone())]]).into(),
        ))
    }

    pub(crate) fn unary_anonymous_function_param_set(func: &Obj) -> Option<Obj> {
        let af: &AnonymousFn = match func {
            Obj::AnonymousFn(af) => af,
            Obj::FnObj(fo) => {
                if !fo.body.is_empty() {
                    return None;
                }
                match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => return None,
                }
            }
            _ => return None,
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return None;
        }
        let param_names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
        let param_name = param_names.first()?;
        Self::set_for_unary_param(&af.body.params_def_with_set, param_name.as_str())
    }

    fn verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
        &mut self,
        param_name: String,
        set: Obj,
        then_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![param_name],
                ParamType::Obj(set),
            )]);
            rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
            rt.verify_atomic_fact_by_known_atomic_or_builtin_only(then_fact, verify_state)
        })
    }

    fn finite_set_enumeration_summand_shape(
        &mut self,
        sum: &Sum,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<FiniteSetEnumerationSummand>, RuntimeError> {
        let af = match sum.func.as_ref() {
            Obj::AnonymousFn(af) => af,
            Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let param_names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
        let Some(param_name) = param_names.first() else {
            return Ok(None);
        };
        let Some(index_set) =
            Self::set_for_unary_param(&af.body.params_def_with_set, param_name.as_str())
        else {
            return Ok(None);
        };
        let sum_index_set: Obj =
            ClosedRange::new(sum.start.as_ref().clone(), sum.end.as_ref().clone()).into();
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &index_set,
                &sum_index_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        let Obj::FnObj(outer_call) = af.equal_to.as_ref() else {
            return Ok(None);
        };
        if outer_call.body.len() != 1 || outer_call.body[0].len() != 1 {
            return Ok(None);
        }
        let Obj::FnObj(enumerator_call) = outer_call.body[0][0].as_ref() else {
            return Ok(None);
        };
        if enumerator_call.body.len() != 1 || enumerator_call.body[0].len() != 1 {
            return Ok(None);
        }
        let index_obj = obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::FnSet);
        if !verify_equality_by_they_are_the_same(enumerator_call.body[0][0].as_ref(), &index_obj) {
            return Ok(None);
        }

        let outer_function: Obj = outer_call.head.as_ref().clone().into();
        let enumerator: Obj = enumerator_call.head.as_ref().clone().into();
        let Some(outer_body) = self.get_fn_range_on_function_body(&outer_function) else {
            return Ok(None);
        };
        if ParamGroupWithSet::number_of_params(&outer_body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let outer_param_names =
            ParamGroupWithSet::collect_param_names(&outer_body.params_def_with_set);
        let Some(outer_param_name) = outer_param_names.first() else {
            return Ok(None);
        };
        let Some(target_set) =
            Self::set_for_unary_param(&outer_body.params_def_with_set, outer_param_name.as_str())
        else {
            return Ok(None);
        };

        let Some(enumerator_body) = self.get_fn_range_on_function_body(&enumerator) else {
            return Ok(None);
        };
        if ParamGroupWithSet::number_of_params(&enumerator_body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let enumerator_param_names =
            ParamGroupWithSet::collect_param_names(&enumerator_body.params_def_with_set);
        let Some(enumerator_param_name) = enumerator_param_names.first() else {
            return Ok(None);
        };
        let Some(enumerator_index_set) = Self::set_for_unary_param(
            &enumerator_body.params_def_with_set,
            enumerator_param_name.as_str(),
        ) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &enumerator_index_set,
                &index_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                enumerator_body.ret_set.as_ref(),
                &target_set,
                line_file,
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        Ok(Some(FiniteSetEnumerationSummand {
            outer_function,
            enumerator_head: enumerator_call.head.as_ref().clone(),
            index_set,
            target_set,
        }))
    }

    fn verify_unique_preimage_enumerator_fact(
        &mut self,
        shape: &FiniteSetEnumerationSummand,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let x_name = self.generate_random_unused_name();
        let i_name = format!("{}_idx", x_name);
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let i_obj = obj_for_bound_param_in_scope(i_name.clone(), ParamObjType::Exist);
        let enumerator_at_i: Obj =
            FnObj::new(shape.enumerator_head.clone(), vec![vec![Box::new(i_obj)]]).into();
        let body_fact: AtomicFact =
            EqualFact::new(enumerator_at_i, x_obj, line_file.clone()).into();
        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![i_name],
                ParamType::Obj(shape.index_set.clone()),
            )]),
            vec![ExistBodyFact::AtomicFact(body_fact)],
            line_file.clone(),
        )?;
        let forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_name],
                ParamType::Obj(shape.target_set.clone()),
            )]),
            vec![],
            vec![ExistFactEnum::ExistUniqueFact(exist_body).into()],
            line_file,
        )?;
        let fact: Fact = forall_fact.into();
        let result = self.verify_fact_full(&fact, verify_state)?;
        Ok(result.is_true())
    }

    fn set_for_unary_param(params_def: &ParamDefWithSet, param_name: &str) -> Option<Obj> {
        for group in params_def.iter() {
            if group.params.iter().any(|p| p == param_name) {
                return Some(group.set_obj().clone());
            }
        }
        None
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

struct FiniteSetEnumerationSummand {
    outer_function: Obj,
    enumerator_head: FnObjHead,
    index_set: Obj,
    target_set: Obj,
}

struct NestedFiniteSetSumCartesianShape {
    product_set: Obj,
    function: Obj,
}
