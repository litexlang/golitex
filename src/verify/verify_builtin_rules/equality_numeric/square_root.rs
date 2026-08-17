use super::*;

impl Runtime {
    // Principal square-root identity: `(sqrt(x))^2 = x` for real `x >= 0`.
    // Example: `forall x R: x >= 0 =>: (sqrt(x))^2 = x`.
    pub(crate) fn try_verify_sqrt_square_identity(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
        let arg_result = self.verify_equal_fact_as_builtin_premise(
            &EqualFact::new_from_refs(sqrt.arg.as_ref(), other, line_file.clone()),
            builtin_state,
        )?;
        if !arg_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
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
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (sqrt, other) = match (left, right) {
            (Obj::Sqrt(sqrt), other) => (sqrt, other),
            (other, Obj::Sqrt(sqrt)) => (sqrt, other),
            _ => return Ok(None),
        };
        for literal in [
            Number::new("0".to_string()).into(),
            Number::new("1".to_string()).into(),
        ] {
            let arg_result = self.verify_equal_fact_as_builtin_premise(
                &EqualFact::new_from_refs(sqrt.arg.as_ref(), &literal, line_file.clone()),
                builtin_state,
            )?;
            if !arg_result.is_true() {
                continue;
            }
            let other_result = self.verify_equal_fact_as_builtin_premise(
                &EqualFact::new_from_refs(other, &literal, line_file.clone()),
                builtin_state,
            )?;
            if !other_result.is_true() {
                continue;
            }
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "sqrt: sqrt(0) = 0 and sqrt(1) = 1".to_string(),
                    vec![arg_result, other_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // Principal square root of a square returns the nonnegative root.
    // Example: from `a >= 0` and `x = a^2`, prove `sqrt(x) = a`.
    pub(crate) fn try_verify_sqrt_of_square_identity(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
        let other_squared: Obj =
            Pow::new(other.clone(), Number::new("2".to_string()).into()).into();
        let square: AtomicFact =
            EqualFact::new_from_refs(sqrt.arg.as_ref(), &other_squared, line_file.clone()).into();
        let Some(results) =
            self.verify_builtin_rule_premises(&[nonnegative, square], builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "sqrt: sqrt(a^2) = a for a >= 0".to_string(),
                results,
            )
            .into(),
        ))
    }

    // Square root distributes over products of nonnegative factors.
    // Example: from `a >= 0`, `b >= 0`, and `x = a * b`, prove
    // `sqrt(x) = sqrt(a) * sqrt(b)`.
    pub(crate) fn try_verify_sqrt_product_identity(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
        let right_nonnegative: AtomicFact = LessEqualFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            right_factor.arg.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let arg_product: Obj = Mul::new(
            left_factor.arg.as_ref().clone(),
            right_factor.arg.as_ref().clone(),
        )
        .into();
        let arg_product_fact: AtomicFact =
            EqualFact::new_from_refs(sqrt.arg.as_ref(), &arg_product, line_file.clone()).into();
        let arg_product_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&arg_product_fact, builtin_state)?;
        let results = if arg_product_result.is_true() {
            let Some(mut results) = self.verify_builtin_rule_premises(
                &[left_nonnegative, right_nonnegative],
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            results.push(arg_product_result);
            results
        } else {
            let Some(results) = self.verify_builtin_rule_premises(
                &[left_nonnegative, right_nonnegative, arg_product_fact],
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            results
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "sqrt: sqrt(a * b) = sqrt(a) * sqrt(b)".to_string(),
                results,
            )
            .into(),
        ))
    }

    // Square root distributes over quotients with nonnegative numerator and positive denominator.
    // Example: from `a >= 0`, `b > 0`, and `x = a / b`, prove
    // `sqrt(x) = sqrt(a) / sqrt(b)`.
    pub(crate) fn try_verify_sqrt_quotient_identity(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
        let denominator_positive: AtomicFact = LessFact::new(
            Self::literal_zero_obj_for_abs_builtin(),
            denominator_sqrt.arg.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let arg_quotient: Obj = Div::new(
            numerator_sqrt.arg.as_ref().clone(),
            denominator_sqrt.arg.as_ref().clone(),
        )
        .into();
        let arg_quotient_fact: AtomicFact =
            EqualFact::new_from_refs(sqrt.arg.as_ref(), &arg_quotient, line_file.clone()).into();
        let arg_quotient_result =
            self.verify_atomic_fact_as_builtin_rule_premise(&arg_quotient_fact, builtin_state)?;
        let results = if arg_quotient_result.is_true() {
            let Some(mut results) = self.verify_builtin_rule_premises(
                &[numerator_nonnegative, denominator_positive],
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            results.push(arg_quotient_result);
            results
        } else {
            let Some(results) = self.verify_builtin_rule_premises(
                &[
                    numerator_nonnegative,
                    denominator_positive,
                    arg_quotient_fact,
                ],
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            results
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "sqrt: sqrt(a / b) = sqrt(a) / sqrt(b)".to_string(),
                results,
            )
            .into(),
        ))
    }

    pub(crate) fn try_verify_sqrt_equalities(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) = self.try_verify_sqrt_square_identity(equal_fact, builtin_state)? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_sqrt_zero_one_identity(equal_fact, builtin_state)? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_sqrt_of_square_identity(equal_fact, builtin_state)? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_sqrt_product_identity(equal_fact, builtin_state)? {
            return Ok(Some(done));
        }
        if let Some(done) = self.try_verify_sqrt_quotient_identity(equal_fact, builtin_state)? {
            return Ok(Some(done));
        }
        Ok(None)
    }
}
