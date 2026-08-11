use super::*;

impl Runtime {
    pub(super) fn literal_one_obj_for_log_builtin() -> Obj {
        Obj::Number(Number::new("1".to_string()))
    }

    pub(super) fn literal_neg_one_obj_for_log_builtin() -> Obj {
        Obj::Number(Number::new("-1".to_string()))
    }

    pub(super) fn literal_zero_obj_for_abs_builtin() -> Obj {
        Obj::Number(Number::new("0".to_string()))
    }

    pub(super) fn obj_is_literal_neg_one_for_abs_builtin(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "-1",
            _ => false,
        }
    }

    pub(super) fn obj_is_negation_of_for_abs_builtin(obj: &Obj, expected_arg: &Obj) -> bool {
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

    pub(super) fn obj_is_abs_product_for_abs_builtin(obj: &Obj, x: &Obj, y: &Obj) -> bool {
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

    pub(super) fn try_verify_abs_nonnegative_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let mut nonnegative_result =
            self.verify_builtin_rule_premise(&nonnegative, builtin_state)?;
        if !nonnegative_result.is_true() {
            let positive: AtomicFact = LessFact::new(
                Self::literal_zero_obj_for_abs_builtin(),
                arg.clone(),
                line_file.clone(),
            )
            .into();
            nonnegative_result = self.verify_builtin_rule_premise(&positive, builtin_state)?;
        }
        if !nonnegative_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "abs: abs(x) = x from 0 <= x".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(AbsoluteValueBuiltinRule::NonnegativeIdentity),
                vec![nonnegative_result],
            )
            .into(),
        ))
    }

    pub(super) fn try_verify_abs_nonpositive_negation(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let mut nonpositive_result =
            self.verify_builtin_rule_premise(&nonpositive, builtin_state)?;
        if !nonpositive_result.is_true() {
            let negative: AtomicFact = LessFact::new(
                arg.clone(),
                Self::literal_zero_obj_for_abs_builtin(),
                line_file.clone(),
            )
            .into();
            nonpositive_result = self.verify_builtin_rule_premise(&negative, builtin_state)?;
        }
        if !nonpositive_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "abs: abs(x) = -x from x <= 0".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(AbsoluteValueBuiltinRule::NonpositiveNegation),
                vec![nonpositive_result],
            )
            .into(),
        ))
    }

    pub(super) fn try_verify_abs_product(
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
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "abs: abs(x * y) = abs(x) * abs(y)".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(AbsoluteValueBuiltinRule::Product),
                Vec::new(),
            )
            .into(),
        ))
    }

    // Even powers ignore sign, so `x^2 = abs(x)^2`.
    // Example: `forall x R: x ^ 4 = abs(x) ^ 4`.
    pub(super) fn try_verify_abs_even_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
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

        let (bases_match, real_base) = match (left_pow.base.as_ref(), right_pow.base.as_ref()) {
            (Obj::Abs(abs), other) => (
                objs_equal_by_display_string(abs.arg.as_ref(), other),
                abs.arg.as_ref(),
            ),
            (other, Obj::Abs(abs)) => (
                objs_equal_by_display_string(other, abs.arg.as_ref()),
                abs.arg.as_ref(),
            ),
            _ => return Ok(None),
        };
        if !bases_match {
            return Ok(None);
        }
        let Some(steps) = self.verify_objects_are_known_reals_in_builtin(
            &[real_base],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            left,
            right,
            line_file,
            "abs: x^n = abs(x)^n for even integer n",
            steps,
        )))
    }

    pub(super) fn try_verify_zero_from_abs_zero(
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
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_abs_nonnegative_identity(left, right, line_file.clone(), builtin_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_abs_nonpositive_negation(left, right, line_file.clone(), builtin_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_abs_product(left, right, line_file.clone())? {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_abs_even_power(left, right, line_file.clone(), builtin_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_zero_from_abs_zero(left, right, line_file)? {
            return Ok(Some(done));
        }
        Ok(None)
    }
}
