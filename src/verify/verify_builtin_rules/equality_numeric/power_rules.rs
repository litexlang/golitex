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
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Pow(pow) = factor else {
            if !Self::obj_is_builtin_literal_one(exponent) {
                return Ok(false);
            }
            return Ok(self
                .verify_equal_fact_as_builtin_premise(
                    &EqualFact::new_from_refs(base, factor, line_file.clone()),
                    builtin_state,
                )?
                .is_true());
        };
        if !self
            .verify_equal_fact_as_builtin_premise(
                &EqualFact::new_from_refs(base, pow.base.as_ref(), line_file.clone()),
                builtin_state,
            )?
            .is_true()
        {
            return Ok(false);
        }
        Ok(self
            .verify_equal_fact_as_builtin_premise(
                &EqualFact::new_from_refs(exponent, pow.exponent.as_ref(), line_file.clone()),
                builtin_state,
            )?
            .is_true())
    }

    pub(super) fn obj_is_verified_in_n_pos(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let in_n_pos: AtomicFact =
            InFact::new(obj.clone(), StandardSet::NPos.into(), line_file).into();
        Ok(self
            .verify_builtin_rule_premise(&in_n_pos, builtin_state)?
            .is_true())
    }

    pub(super) fn obj_is_verified_in_standard_set_for_power_builtin(
        &mut self,
        obj: &Obj,
        standard_set: StandardSet,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let in_set: AtomicFact =
            InFact::new(obj.clone(), standard_set.clone().into(), line_file.clone()).into();
        if self
            .verify_builtin_rule_premise(&in_set, builtin_state)?
            .is_true()
        {
            return Ok(true);
        }

        for known_set in self.known_sets_containing_obj(obj) {
            let Obj::StandardSet(known_standard_set) = &known_set else {
                continue;
            };
            if !known_standard_set.is_subset_eq(&standard_set) {
                continue;
            }
            let known_membership: AtomicFact =
                InFact::new(obj.clone(), known_set, line_file.clone()).into();
            if self
                .verify_non_equational_atomic_fact_with_known_atomic_facts(&known_membership)?
                .is_true()
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn obj_is_verified_integer_exponent_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        if let Obj::Number(number) = obj {
            return Ok(is_integer_after_simplification(number));
        }

        // Integer arithmetic remains an integer exponent even when its carrier
        // has not been materialized as a separate fact. Keeping this structural
        // check inside the power rule avoids a forbidden second builtin hop in
        // induction hypotheses such as `2^(n - 1)`.
        let integer_operands = match obj {
            Obj::Add(add) => Some((add.left.as_ref(), add.right.as_ref())),
            Obj::Sub(sub) => Some((sub.left.as_ref(), sub.right.as_ref())),
            Obj::Mul(mul) => Some((mul.left.as_ref(), mul.right.as_ref())),
            _ => None,
        };
        if let Some((left, right)) = integer_operands {
            return Ok(self.obj_is_verified_integer_exponent_for_power_builtin(
                left,
                line_file.clone(),
                builtin_state,
            )? && self.obj_is_verified_integer_exponent_for_power_builtin(
                right,
                line_file,
                builtin_state,
            )?);
        }

        if self.obj_is_verified_in_standard_set_for_power_builtin(
            obj,
            StandardSet::Z,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(true);
        }
        self.obj_is_verified_in_standard_set_for_power_builtin(
            obj,
            StandardSet::N,
            line_file,
            builtin_state,
        )
    }

    fn obj_is_verified_real_exponent_for_power_of_power(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        if self.obj_is_verified_in_standard_set_for_power_builtin(
            obj,
            StandardSet::R,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(true);
        }

        let Obj::Div(div) = obj else {
            return Ok(false);
        };
        if !Self::obj_is_builtin_literal_one(div.left.as_ref()) {
            return Ok(false);
        }
        self.obj_is_verified_in_standard_set_for_power_builtin(
            div.right.as_ref(),
            StandardSet::RStar,
            line_file,
            builtin_state,
        )
    }

    fn obj_is_verified_positive_real_base_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        if self.obj_is_verified_in_standard_set_for_power_builtin(
            obj,
            StandardSet::RPos,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(true);
        }
        let in_r: AtomicFact =
            InFact::new(obj.clone(), StandardSet::R.into(), line_file.clone()).into();
        if !self
            .verify_builtin_rule_premise(&in_r, builtin_state)?
            .is_true()
        {
            return Ok(false);
        }
        let positive: AtomicFact =
            LessFact::new(Number::new("0".to_string()).into(), obj.clone(), line_file).into();
        Ok(self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&positive)?
            .is_true())
    }

    pub(super) fn obj_is_verified_nonzero_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let nonzero: AtomicFact = NotEqualFact::new(
            obj.clone(),
            Self::literal_zero_obj_for_abs_builtin(),
            line_file,
        )
        .into();
        Ok(self
            .verify_builtin_rule_premise(&nonzero, builtin_state)?
            .is_true())
    }

    pub(super) fn power_addition_exponent_rule_holds_one_direction(
        &mut self,
        combined_power: &Pow,
        product: &Mul,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Add(add_exponent) = combined_power.exponent.as_ref() else {
            return Ok(false);
        };

        // Power law for positive integer exponents:
        // `a^(m+n) = a^m * a^n`. Example: `forall a R, m, n N+: a^(m+n) = a^m * a^n`.
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
                builtin_state,
            )? {
                continue;
            }
            if !self.power_factor_matches_base_and_exponent(
                right_factor,
                combined_power.base.as_ref(),
                right_exp,
                line_file.clone(),
                builtin_state,
            )? {
                continue;
            }
            let exponents_are_positive =
                self.obj_is_verified_in_n_pos(left_exp, line_file.clone(), builtin_state)?
                    && self.obj_is_verified_in_n_pos(
                        right_exp,
                        line_file.clone(),
                        builtin_state,
                    )?;
            if exponents_are_positive {
                return Ok(true);
            }

            // Natural-exponent power law for complex bases:
            // `a^(m+n) = a^m * a^n`, including the cases m=0 or n=0.
            // Example: `forall a C, m, n N: a^m * a^n = a^(m+n)`.
            let exponents_are_natural = self.obj_is_verified_in_standard_set_for_power_builtin(
                left_exp,
                StandardSet::N,
                line_file.clone(),
                builtin_state,
            )? && self
                .obj_is_verified_in_standard_set_for_power_builtin(
                    right_exp,
                    StandardSet::N,
                    line_file.clone(),
                    builtin_state,
                )?;
            if exponents_are_natural {
                let base_in_c = self.obj_is_verified_in_standard_set_for_power_builtin(
                    combined_power.base.as_ref(),
                    StandardSet::C,
                    line_file.clone(),
                    builtin_state,
                )?;
                if base_in_c {
                    return Ok(true);
                }
            }

            // Real-exponent addition law requires a positive real base.
            // Example: `forall a R+, m, n R: a^(m+n) = a^m * a^n`.
            let exponents_are_real = self.obj_is_verified_in_standard_set_for_power_builtin(
                left_exp,
                StandardSet::R,
                line_file.clone(),
                builtin_state,
            )? && self.obj_is_verified_in_standard_set_for_power_builtin(
                right_exp,
                StandardSet::R,
                line_file.clone(),
                builtin_state,
            )?;
            if exponents_are_real
                && self.obj_is_verified_in_standard_set_for_power_builtin(
                    combined_power.base.as_ref(),
                    StandardSet::RPos,
                    line_file.clone(),
                    builtin_state,
                )?
            {
                return Ok(true);
            }

            // The remaining integer-exponent branch needs a nonzero base so negative
            // exponents do not accidentally justify undefined `0^(-n)`.
            // Example: `forall a R*, m, n Z: a^m * a^n = a^(m+n)`.
            let exponents_are_integer = self.obj_is_verified_integer_exponent_for_power_builtin(
                left_exp,
                line_file.clone(),
                builtin_state,
            )? && self
                .obj_is_verified_integer_exponent_for_power_builtin(
                    right_exp,
                    line_file.clone(),
                    builtin_state,
                )?;
            if !exponents_are_integer {
                return Ok(false);
            }
            if !self.obj_is_verified_nonzero_for_power_builtin(
                combined_power.base.as_ref(),
                line_file.clone(),
                builtin_state,
            )? {
                return Ok(false);
            }
            return Ok(true);
        }

        Ok(false)
    }

    pub(crate) fn try_verify_power_addition_exponent_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let holds = match (left, right) {
            (Obj::Pow(pow), Obj::Mul(product)) => self
                .power_addition_exponent_rule_holds_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    builtin_state,
                )?,
            (Obj::Mul(product), Obj::Pow(pow)) => self
                .power_addition_exponent_rule_holds_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    builtin_state,
                )?,
            _ => false,
        };
        if holds {
            return Ok(Some(factual_equal_success_by_builtin_reason(equal_fact, "equality: a^(m+n) = a^m * a^n for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base")));
        }
        Ok(None)
    }

    pub(super) fn power_of_power_rule_holds_one_direction(
        &mut self,
        nested_power: &Pow,
        combined_power: &Pow,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Pow(inner_power) = nested_power.base.as_ref() else {
            return Ok(false);
        };
        if !self
            .verify_equal_fact_as_builtin_premise(
                &EqualFact::new_from_refs(
                    inner_power.base.as_ref(),
                    combined_power.base.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
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
        if !self.power_exponent_product_matches(
            inner_power.exponent.as_ref(),
            nested_power.exponent.as_ref(),
            &multiplied_exponent,
            combined_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(false);
        }

        // Real-exponent power-of-power law requires a positive real base.
        // Example: `forall a R+, m, n R: (a^m)^n = a^(m*n)`.
        let base_is_positive_real = self.obj_is_verified_positive_real_base_for_power_builtin(
            combined_power.base.as_ref(),
            line_file.clone(),
            builtin_state,
        )?;
        let exponents_are_real = self.obj_is_verified_real_exponent_for_power_of_power(
            inner_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )? && self.obj_is_verified_real_exponent_for_power_of_power(
            nested_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )?;
        if base_is_positive_real && exponents_are_real {
            return Ok(true);
        }

        // Power-of-power law for positive integer exponents:
        // `(a^m)^n = a^(m*n)`. Example: `forall a R, m, n N+: (a^m)^n = a^(m*n)`.
        let exponents_are_positive = self.obj_is_verified_in_n_pos(
            inner_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )? && self.obj_is_verified_in_n_pos(
            nested_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )?;
        if exponents_are_positive {
            return Ok(true);
        }

        // Natural-exponent power-of-power law over complex bases, including zero exponents.
        // Example: `forall a C, m, n N: (a^m)^n = a^(m*n)`.
        let exponents_are_natural = self.obj_is_verified_in_standard_set_for_power_builtin(
            inner_power.exponent.as_ref(),
            StandardSet::N,
            line_file.clone(),
            builtin_state,
        )? && self.obj_is_verified_in_standard_set_for_power_builtin(
            nested_power.exponent.as_ref(),
            StandardSet::N,
            line_file.clone(),
            builtin_state,
        )?;
        if exponents_are_natural
            && self.obj_is_verified_in_standard_set_for_power_builtin(
                combined_power.base.as_ref(),
                StandardSet::C,
                line_file.clone(),
                builtin_state,
            )?
        {
            return Ok(true);
        }

        // Integer-exponent power-of-power law needs a nonzero base so negative
        // exponents do not justify undefined powers of zero.
        // Example: `forall a R*, m, n Z: (a^m)^n = a^(m*n)`.
        let exponents_are_integer = self.obj_is_verified_integer_exponent_for_power_builtin(
            inner_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )? && self.obj_is_verified_integer_exponent_for_power_builtin(
            nested_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )?;
        if !exponents_are_integer {
            return Ok(false);
        }
        self.obj_is_verified_nonzero_for_power_builtin(
            combined_power.base.as_ref(),
            line_file,
            builtin_state,
        )
    }

    fn power_exponent_product_matches(
        &mut self,
        left_factor: &Obj,
        right_factor: &Obj,
        product: &Obj,
        expected: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        if self
            .verify_equal_fact_as_builtin_premise(
                &EqualFact::new_from_refs(product, expected, line_file.clone()),
                builtin_state,
            )?
            .is_true()
        {
            return Ok(true);
        }
        if !Self::obj_is_builtin_literal_one(expected) {
            return Ok(false);
        }
        fn reciprocal_base(factor: &Obj) -> Option<&Obj> {
            let Obj::Div(div) = factor else {
                return None;
            };
            Runtime::obj_is_builtin_literal_one(div.left.as_ref()).then_some(div.right.as_ref())
        }
        let base = if let Some(base) = reciprocal_base(right_factor) {
            (left_factor.to_string() == base.to_string()).then_some(base)
        } else if let Some(base) = reciprocal_base(left_factor) {
            (right_factor.to_string() == base.to_string()).then_some(base)
        } else {
            None
        };
        let Some(base) = base else {
            return Ok(false);
        };
        self.obj_is_verified_nonzero_for_power_builtin(base, line_file, builtin_state)
    }

    // A power of a power can equal the bare base when the exponents multiply to one.
    // Example: for `a R+` and `b R*`, `(a^b)^(1 / b) = a`.
    fn power_of_power_equals_base_holds(
        &mut self,
        nested_power: &Pow,
        base: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        let combined_power = Pow::new(base.clone(), one);
        self.power_of_power_rule_holds_one_direction(
            nested_power,
            &combined_power,
            line_file,
            builtin_state,
        )
    }

    pub(crate) fn try_verify_power_of_power_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let holds = match (left, right) {
            (Obj::Pow(left_power), Obj::Pow(right_power)) => {
                self.power_of_power_rule_holds_one_direction(
                    left_power,
                    right_power,
                    line_file.clone(),
                    builtin_state,
                )? || self.power_of_power_rule_holds_one_direction(
                    right_power,
                    left_power,
                    line_file.clone(),
                    builtin_state,
                )?
            }
            (Obj::Pow(nested_power), base) => self.power_of_power_equals_base_holds(
                nested_power,
                base,
                line_file.clone(),
                builtin_state,
            )?,
            (base, Obj::Pow(nested_power)) => self.power_of_power_equals_base_holds(
                nested_power,
                base,
                line_file.clone(),
                builtin_state,
            )?,
            _ => false,
        };
        if holds {
            return Ok(Some(factual_equal_success_by_builtin_reason(equal_fact, "equality: (a^m)^n = a^(m*n) for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base")));
        }
        Ok(None)
    }

    pub(super) fn power_product_rule_holds_one_direction(
        &mut self,
        combined_power: &Pow,
        product: &Mul,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Mul(combined_base) = combined_power.base.as_ref() else {
            return Ok(false);
        };
        let exponent_in_n_pos = self.obj_is_verified_in_n_pos(
            combined_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )?;
        if !exponent_in_n_pos {
            // Product power law for real exponents over positive real factors:
            // `(a*b)^x = a^x*b^x`. Example: `forall a,b R+, x R: (a*b)^x = a^x*b^x`.
            let exponent_is_real = self.obj_is_verified_in_standard_set_for_power_builtin(
                combined_power.exponent.as_ref(),
                StandardSet::R,
                line_file.clone(),
                builtin_state,
            )?;
            let real_exponent_over_positive_real_bases = if exponent_is_real {
                let left_base_is_positive_real = self
                    .obj_is_verified_positive_real_base_for_power_builtin(
                        combined_base.left.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?;
                let right_base_is_positive_real = self
                    .obj_is_verified_positive_real_base_for_power_builtin(
                        combined_base.right.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?;
                left_base_is_positive_real && right_base_is_positive_real
            } else {
                false
            };

            let exponent_in_n = self.obj_is_verified_in_standard_set_for_power_builtin(
                combined_power.exponent.as_ref(),
                StandardSet::N,
                line_file.clone(),
                builtin_state,
            )?;
            let natural_exponent_over_complex_bases = if exponent_in_n {
                let left_base_in_c = self.obj_is_verified_in_standard_set_for_power_builtin(
                    combined_base.left.as_ref(),
                    StandardSet::C,
                    line_file.clone(),
                    builtin_state,
                )?;
                let right_base_in_c = self.obj_is_verified_in_standard_set_for_power_builtin(
                    combined_base.right.as_ref(),
                    StandardSet::C,
                    line_file.clone(),
                    builtin_state,
                )?;
                left_base_in_c && right_base_in_c
            } else {
                false
            };

            let integer_exponent_over_nonzero_bases = if natural_exponent_over_complex_bases {
                false
            } else {
                let exponent_is_integer = self.obj_is_verified_integer_exponent_for_power_builtin(
                    combined_power.exponent.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?;
                if !exponent_is_integer {
                    false
                } else {
                    let left_base_nonzero = self.obj_is_verified_nonzero_for_power_builtin(
                        combined_base.left.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?;
                    let right_base_nonzero = self.obj_is_verified_nonzero_for_power_builtin(
                        combined_base.right.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?;
                    // Nonzeroness of the product is a consequence of the two immediate
                    // factor requirements, not a second builtin-rule premise.
                    left_base_nonzero && right_base_nonzero
                }
            };

            if !real_exponent_over_positive_real_bases
                && !natural_exponent_over_complex_bases
                && !integer_exponent_over_nonzero_bases
            {
                return Ok(false);
            }
        }

        // Product power law for natural integer exponents over complex bases, and the
        // existing positive-integer exponent shape; integer exponents need nonzero
        // factors so negative powers are defined.
        // Example: `forall a,b R*, n Z: (a*b)^n = a^n*b^n`.
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
                builtin_state,
            )? {
                continue;
            }
            if !self.power_factor_matches_base_and_exponent(
                right_factor,
                right_base,
                combined_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )? {
                continue;
            }
            return Ok(true);
        }

        Ok(false)
    }

    pub(crate) fn try_verify_power_product_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let holds = match (left, right) {
            (Obj::Pow(pow), Obj::Mul(product)) => self.power_product_rule_holds_one_direction(
                pow,
                product,
                line_file.clone(),
                builtin_state,
            )?,
            (Obj::Mul(product), Obj::Pow(pow)) => self.power_product_rule_holds_one_direction(
                pow,
                product,
                line_file.clone(),
                builtin_state,
            )?,
            _ => false,
        };
        if holds {
            return Ok(Some(factual_equal_success_by_builtin_reason(equal_fact, "equality: (a*b)^x = a^x * b^x for real x over positive real factors, n in N over complex bases, n in N+, or n in Z with nonzero bases")));
        }
        Ok(None)
    }
}
