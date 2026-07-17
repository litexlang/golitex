use super::*;

impl Runtime {
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

    pub(super) fn collect_known_equal_power_exponents_for_bases(
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

    pub(super) fn positive_exponent_from_negated_power_exponent(exponent: &Obj) -> Option<Obj> {
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

    pub(super) fn power_inverse_rule_holds_one_direction(
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

    pub(super) fn reciprocal_positive_integer_denominator_for_power_root_builtin(
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
}
