use super::*;

impl Runtime {
    pub(super) fn obj_is_builtin_literal_zero(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => matches!(
                compare_normalized_number_str_to_zero(&n.normalized_value),
                NumberCompareResult::Equal
            ),
            _ => false,
        }
    }

    pub(super) fn obj_is_builtin_literal_one(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "1",
            _ => false,
        }
    }

    pub(super) fn obj_is_builtin_literal_neg_one(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "-1",
            _ => false,
        }
    }

    // Literal 0 vs `x - y`: verify the equality if `x = y` holds via the full equality pipeline.
    pub(crate) fn try_verify_zero_equals_subtraction_implies_equal_operands(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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

        let inner = self.verify_equal_fact_as_builtin_premise(
            &EqualFact::new_from_refs(x, y, line_file.clone()),
            builtin_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                equal_fact,
                "equality: 0 = x - y with x = y (known or builtin)",
            )));
        }
        Ok(None)
    }

    // Zero-product cancellation: from `a * b = 0` and `a != 0`, infer `b = 0` (and symmetrically).
    // Example: from `(x - 1) * y = 0` and `x - 1 != 0`, prove `y = 0`.
    pub(crate) fn verify_zero_product_factor_matches_target(
        &mut self,
        target: &Obj,
        factor: &Obj,
        line_file: LineFile,
        _builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Do not call the full equality builtin here; that would re-enter zero-product
        // cancellation while this rule is already trying to match a factor.
        let known_result = self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
            target,
            factor,
            line_file.clone(),
        ));
        if known_result.is_true() {
            return Ok(known_result);
        }

        let calculation_result = self.verify_equal_fact_by_direct_evaluation(&EqualFact::new(
            target.clone(),
            factor.clone(),
            line_file.clone(),
        ));
        if calculation_result.is_true() {
            return Ok(calculation_result);
        }

        Ok(StmtResult::Unknown(StmtUnknown::new()))
    }

    pub(crate) fn try_verify_zero_equals_product_implies_other_factor_zero(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
                    builtin_state,
                )?;
                if left_target_result.is_true() {
                    let right_nonzero: AtomicFact = NotEqualFact::new(
                        mul.right.as_ref().clone(),
                        zero_obj.clone(),
                        line_file.clone(),
                    )
                    .into();
                    let right_nonzero_result =
                        self.verify_builtin_rule_premise(&right_nonzero, builtin_state)?;
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
                    builtin_state,
                )?;
                if right_target_result.is_true() {
                    let left_nonzero: AtomicFact = NotEqualFact::new(
                        mul.left.as_ref().clone(),
                        zero_obj.clone(),
                        line_file.clone(),
                    )
                    .into();
                    let left_nonzero_result =
                        self.verify_builtin_rule_premise(&left_nonzero, builtin_state)?;
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
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
        let inner = self.verify_equal_fact_as_builtin_premise(
            &EqualFact::new_from_refs(base, zero_side, line_file.clone()),
            builtin_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                equal_fact,
                "equality: 0 = a^n from a = 0, n positive integer literal",
            )));
        }
        Ok(None)
    }

    // Zero is divisible by every non-zero integer modulus: `0 % m = 0`.
    // Example: `forall m Z: m != 0 =>: 0 % m = 0`.
    pub(crate) fn try_verify_zero_mod_equals_zero(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
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
            equal_fact,
            "equality: 0 % m = 0",
        )))
    }

    // Every integer is congruent to zero modulo one: `x % 1 = 0`.
    // This is the m = 1 version of the complete residue rule; no `or` is needed.
    // Example: `forall x Z: x % 1 = 0`.
    pub(crate) fn try_verify_mod_one_equals_zero(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
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
            equal_fact,
            "equality: x % 1 = 0",
        )))
    }

    // One has remainder one modulo every integer modulus at least two.
    // Example: `k >= 2` => `1 % k = 1`.
    pub(crate) fn try_verify_one_mod_equals_one_for_modulus_at_least_two(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let modulus = if Self::obj_is_builtin_literal_one(left) {
            let Obj::Mod(mod_obj) = right else {
                return Ok(None);
            };
            if !Self::obj_is_builtin_literal_one(mod_obj.left.as_ref()) {
                return Ok(None);
            }
            mod_obj.right.as_ref().clone()
        } else if Self::obj_is_builtin_literal_one(right) {
            let Obj::Mod(mod_obj) = left else {
                return Ok(None);
            };
            if !Self::obj_is_builtin_literal_one(mod_obj.left.as_ref()) {
                return Ok(None);
            }
            mod_obj.right.as_ref().clone()
        } else {
            return Ok(None);
        };

        let modulus_at_least_two: AtomicFact = LessEqualFact::new(
            Number::new("2".to_string()).into(),
            modulus,
            line_file.clone(),
        )
        .into();
        let modulus_result =
            self.verify_builtin_rule_premise(&modulus_at_least_two, builtin_state)?;
        if !modulus_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: 1 % k = 1 for k >= 2".to_string(),
                vec![modulus_result],
            )
            .into(),
        ))
    }

    // Subtracting the Euclidean remainder leaves a multiple of the positive modulus.
    // Example: `forall a Z, b N+: (a - a % b) % b = 0`.
    pub(crate) fn try_verify_mod_dividend_minus_remainder_equals_zero(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
        let dividend_result = self.verify_builtin_rule_premise(&dividend_in_z, builtin_state)?;
        if !dividend_result.is_true() {
            return Ok(None);
        }

        let modulus_in_n_pos: AtomicFact = InFact::new(
            outer_mod.right.as_ref().clone(),
            StandardSet::NPos.into(),
            line_file.clone(),
        )
        .into();
        let modulus_result = self.verify_builtin_rule_premise(&modulus_in_n_pos, builtin_state)?;
        if !modulus_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: (a - a % b) % b = 0 for a in Z and b in N+".to_string(),
                vec![dividend_result, modulus_result],
            )
            .into(),
        ))
    }

    /// Definition of the native Euclidean quotient.
    /// Example: `forall a Z, d N+: a = d * quot(a, d) + a % d`.
    pub(crate) fn try_verify_quot_euclidean_decomposition(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        fn decomposition_parts(side: &Obj) -> Option<(&Obj, &Obj)> {
            let Obj::Add(sum) = side else {
                return None;
            };
            let Obj::Mul(product) = sum.left.as_ref() else {
                return None;
            };
            let Obj::Quot(quot) = product.right.as_ref() else {
                return None;
            };
            let Obj::Mod(remainder) = sum.right.as_ref() else {
                return None;
            };
            if !objs_equal_by_display_string(product.left.as_ref(), quot.right.as_ref())
                || !objs_equal_by_display_string(remainder.left.as_ref(), quot.left.as_ref())
                || !objs_equal_by_display_string(remainder.right.as_ref(), quot.right.as_ref())
            {
                return None;
            }
            Some((quot.left.as_ref(), quot.right.as_ref()))
        }

        let (dividend, divisor) = if let Some((dividend, divisor)) = decomposition_parts(right) {
            if !objs_equal_by_display_string(left, dividend) {
                return Ok(None);
            }
            (dividend, divisor)
        } else if let Some((dividend, divisor)) = decomposition_parts(left) {
            if !objs_equal_by_display_string(right, dividend) {
                return Ok(None);
            }
            (dividend, divisor)
        } else {
            return Ok(None);
        };

        let dividend_in_z: AtomicFact =
            InFact::new(dividend.clone(), StandardSet::Z.into(), line_file.clone()).into();
        let divisor_in_n_pos: AtomicFact =
            InFact::new(divisor.clone(), StandardSet::NPos.into(), line_file.clone()).into();
        let Some(premises) =
            self.verify_builtin_rule_premises(&[dividend_in_z, divisor_in_n_pos], builtin_state)?
        else {
            return Ok(None);
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: Euclidean quotient decomposition a = d * quot(a, d) + a % d".to_string(),
                premises,
            )
            .into(),
        ))
    }

    // Euclidean remainder uniqueness identifies a known bounded remainder with `%`.
    // Example: `a = m * q + r`, `0 <= r < m`, `m > 0` => `a % m = r`.
    pub(crate) fn try_verify_mod_eq_remainder_from_euclidean_division(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (modulus, dividend, remainder) = match (left, right) {
            (Obj::Mod(mod_obj), remainder) => {
                (mod_obj.right.as_ref(), mod_obj.left.as_ref(), remainder)
            }
            (remainder, Obj::Mod(mod_obj)) => {
                (mod_obj.right.as_ref(), mod_obj.left.as_ref(), remainder)
            }
            _ => return Ok(None),
        };

        let candidates = self.get_all_obj_representatives_equal_to_given(dividend);
        for candidate in candidates {
            let Obj::Add(sum) = &candidate else {
                continue;
            };
            let Obj::Mul(product) = sum.left.as_ref() else {
                continue;
            };
            if !objs_equal_by_display_string(product.left.as_ref(), modulus)
                || !objs_equal_by_display_string(sum.right.as_ref(), remainder)
            {
                continue;
            }

            let quotient = product.right.as_ref();
            let divisor_in_n_pos: AtomicFact =
                InFact::new(modulus.clone(), StandardSet::NPos.into(), line_file.clone()).into();
            let remainder_in_n: AtomicFact =
                InFact::new(remainder.clone(), StandardSet::N.into(), line_file.clone()).into();
            let remainder_lt_modulus: AtomicFact =
                LessFact::new(remainder.clone(), modulus.clone(), line_file.clone()).into();

            let Some(integer_steps) = self.verify_objects_are_known_integers_in_builtin_leaf(
                &[dividend, quotient],
                &line_file,
            )?
            else {
                continue;
            };
            let divisor_result =
                self.verify_builtin_rule_premise(&divisor_in_n_pos, builtin_state)?;
            let remainder_result =
                self.verify_builtin_rule_premise(&remainder_in_n, builtin_state)?;
            let bound_result =
                self.verify_builtin_rule_premise(&remainder_lt_modulus, builtin_state)?;
            let decomposition_result = self.verify_equal_fact_by_known_equality(
                &EqualFact::new_from_refs(dividend, &candidate, line_file.clone()),
            );
            if !divisor_result.is_true()
                || !remainder_result.is_true()
                || !bound_result.is_true()
                || !decomposition_result.is_true()
            {
                continue;
            }

            let mut steps = integer_steps;
            steps.extend([
                divisor_result,
                remainder_result,
                bound_result,
                decomposition_result,
            ]);
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "equality: Euclidean remainder uniqueness from a = m * q + r and 0 <= r < m"
                        .to_string(),
                    steps,
                )
                .into(),
            ));
        }

        Ok(None)
    }
}
