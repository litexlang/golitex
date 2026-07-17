use super::*;

impl Runtime {
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
}
