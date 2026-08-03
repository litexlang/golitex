use super::*;

impl Runtime {
    fn verify_direct_positive_real_power_operand(
        &mut self,
        obj: &Obj,
        line_file: &LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let positive: AtomicFact = GreaterFact::new(
            obj.clone(),
            Self::literal_zero_obj_for_abs_builtin(),
            line_file.clone(),
        )
        .into();
        let positive_result = self.verify_builtin_rule_premise(&positive, builtin_state)?;
        if positive_result.is_true() {
            return Ok(Some(positive_result));
        }

        for carrier in [StandardSet::NPos, StandardSet::QPos, StandardSet::RPos] {
            let membership: AtomicFact =
                InFact::new(obj.clone(), carrier.into(), line_file.clone()).into();
            let membership_result = self.verify_builtin_rule_premise(&membership, builtin_state)?;
            if membership_result.is_true() {
                return Ok(Some(membership_result));
            }
        }
        Ok(None)
    }

    // Odd powers of minus one are minus one.
    // Example: `m $in N` proves `(-1)^(2*m+1) = -1`.
    pub(crate) fn try_verify_minus_one_odd_natural_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let is_minus_one = |obj: &Obj| match obj {
            Obj::Number(number) => number.normalized_value == "-1",
            Obj::Mul(mul) => {
                (Self::obj_is_builtin_literal_neg_one(mul.left.as_ref())
                    && Self::obj_is_builtin_literal_one(mul.right.as_ref()))
                    || (Self::obj_is_builtin_literal_one(mul.left.as_ref())
                        && Self::obj_is_builtin_literal_neg_one(mul.right.as_ref()))
            }
            _ => false,
        };
        let pow = if is_minus_one(right) {
            match left {
                Obj::Pow(pow) => pow,
                _ => return Ok(None),
            }
        } else if is_minus_one(left) {
            match right {
                Obj::Pow(pow) => pow,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !is_minus_one(pow.base.as_ref()) {
            return Ok(None);
        }
        let Obj::Add(exponent_sum) = pow.exponent.as_ref() else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_one(exponent_sum.right.as_ref()) {
            return Ok(None);
        }
        let Obj::Mul(even_part) = exponent_sum.left.as_ref() else {
            return Ok(None);
        };
        let m = if Self::obj_is_builtin_literal_two(even_part.left.as_ref()) {
            even_part.right.as_ref()
        } else if Self::obj_is_builtin_literal_two(even_part.right.as_ref()) {
            even_part.left.as_ref()
        } else {
            return Ok(None);
        };
        let m_in_n: AtomicFact =
            InFact::new(m.clone(), StandardSet::N.into(), line_file.clone()).into();
        let m_result = self.verify_builtin_rule_premise(&m_in_n, builtin_state)?;
        if !m_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: (-1)^(2*m+1) = -1 for m in N".to_string(),
                vec![m_result],
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
                builtin_state,
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
    // Example: `forall a C: a^0 = 1`.
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let positive_result =
            self.verify_builtin_rule_premise(&positive_exponent, builtin_state)?;
        let mut positive_steps = Vec::new();
        if positive_result.is_true() {
            positive_steps.push(positive_result);
        } else {
            // Keep reciprocal positivity inside this one power identity rule:
            // direct positivity (or a direct positive carrier) of numerator
            // and denominator entails positivity of their quotient. This lets
            // `n $in N_pos` justify `0^(1/n) = 0` without a second builtin hop.
            let Obj::Div(div) = pow.exponent.as_ref() else {
                return Ok(None);
            };
            let Some(numerator_step) = self.verify_direct_positive_real_power_operand(
                div.left.as_ref(),
                &line_file,
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            let Some(denominator_step) = self.verify_direct_positive_real_power_operand(
                div.right.as_ref(),
                &line_file,
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            positive_steps.extend([numerator_step, denominator_step]);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: 0^x = 0 for x > 0".to_string(),
                positive_steps,
            )
            .into(),
        ))
    }
}
