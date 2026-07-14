use super::*;

impl Runtime {
    pub(super) fn obj_is_builtin_literal_two(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "2",
            _ => false,
        }
    }

    pub(super) fn power_factor_matches_base_and_exponent(
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

    pub(super) fn obj_is_verified_in_n_pos(
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

    pub(super) fn obj_is_verified_in_standard_set_for_power_builtin(
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

    pub(super) fn obj_is_verified_integer_exponent_for_power_builtin(
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

    pub(super) fn obj_is_verified_nonzero_for_power_builtin(
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

    pub(super) fn power_addition_exponent_rule_holds_one_direction(
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

    pub(super) fn power_of_power_rule_holds_one_direction(
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

    pub(super) fn power_product_rule_holds_one_direction(
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
}
