use super::*;

fn combine_power_premise_groups<const N: usize>(
    groups: [Option<Vec<VerifyFactResult>>; N],
) -> Option<Vec<VerifyFactResult>> {
    let mut combined = Vec::new();
    for group in groups {
        combined.append(&mut group?);
    }
    Some(combined)
}

impl Runtime {
    pub(super) fn obj_is_builtin_literal_two(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => n.normalized_value == "2",
            _ => false,
        }
    }

    pub(super) fn try_verify_power_factor_matches_base_and_exponent(
        &mut self,
        factor: &Obj,
        base: &Obj,
        exponent: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let Obj::Pow(pow) = factor else {
            if !Self::obj_is_builtin_literal_one(exponent) {
                return Ok(None);
            }
            return Ok(self
                .try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(base, factor, line_file.clone()),
                    builtin_state,
                )?
                .map(|result| vec![result]));
        };
        let Some(base_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(base, pow.base.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(exponent_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(exponent, pow.exponent.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(vec![base_result, exponent_result]))
    }

    pub(super) fn try_verify_obj_in_n_pos_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let in_n_pos: AtomicFact = self
            .new_in_fact(obj.clone(), StandardSet::NPos.into(), line_file)
            .into();
        Ok(self
            .try_verify_atomic_fact_as_builtin_rule_premise(&in_n_pos, builtin_state)?
            .map(|result| vec![result]))
    }

    pub(super) fn try_verify_obj_in_standard_set_for_power_builtin(
        &mut self,
        obj: &Obj,
        standard_set: StandardSet,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let in_set: AtomicFact = self
            .new_in_fact(obj.clone(), standard_set.clone().into(), line_file.clone())
            .into();
        if let Some(result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_set, builtin_state)?
        {
            return Ok(Some(vec![result]));
        }

        for known_set in self.known_sets_containing_obj(obj) {
            let Obj::StandardSet(known_standard_set) = &known_set else {
                continue;
            };
            if !known_standard_set.is_subset_eq(&standard_set) {
                continue;
            }
            let known_membership: AtomicFact = self
                .new_in_fact(obj.clone(), known_set, line_file.clone())
                .into();
            if let Some(result) = self
                .try_verify_atomic_fact_as_builtin_rule_premise(&known_membership, builtin_state)?
            {
                return Ok(Some(vec![result]));
            }
        }
        Ok(None)
    }

    pub(super) fn try_verify_integer_exponent_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        if let Obj::Number(number) = obj {
            return Ok(is_integer_after_simplification(number).then_some(Vec::new()));
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
            let Some(mut left_results) = self.try_verify_integer_exponent_for_power_builtin(
                left,
                line_file.clone(),
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            let Some(mut right_results) = self.try_verify_integer_exponent_for_power_builtin(
                right,
                line_file,
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            left_results.append(&mut right_results);
            return Ok(Some(left_results));
        }

        if let Some(results) = self.try_verify_obj_in_standard_set_for_power_builtin(
            obj,
            StandardSet::Z,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(Some(results));
        }
        self.try_verify_obj_in_standard_set_for_power_builtin(
            obj,
            StandardSet::N,
            line_file,
            builtin_state,
        )
    }

    fn try_verify_real_exponent_for_power_of_power(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        if let Some(results) = self.try_verify_obj_in_standard_set_for_power_builtin(
            obj,
            StandardSet::R,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(Some(results));
        }

        let Obj::Div(div) = obj else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_one(div.left.as_ref()) {
            return Ok(None);
        }
        self.try_verify_obj_in_standard_set_for_power_builtin(
            div.right.as_ref(),
            StandardSet::RStar,
            line_file,
            builtin_state,
        )
    }

    fn try_verify_positive_real_base_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        if let Some(results) = self.try_verify_obj_in_standard_set_for_power_builtin(
            obj,
            StandardSet::RPos,
            line_file.clone(),
            builtin_state,
        )? {
            return Ok(Some(results));
        }
        let in_r: AtomicFact = self
            .new_in_fact(obj.clone(), StandardSet::R.into(), line_file.clone())
            .into();
        let Some(in_r_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_r, builtin_state)?
        else {
            return Ok(None);
        };
        let positive: AtomicFact = self
            .new_less_fact(Number::new("0".to_string()).into(), obj.clone(), line_file)
            .into();
        let Some(positive_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&positive, builtin_state)?
        else {
            return Ok(None);
        };
        Ok(Some(vec![in_r_result, positive_result]))
    }

    pub(super) fn try_verify_nonzero_for_power_builtin(
        &mut self,
        obj: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let nonzero: AtomicFact = self
            .new_not_equal_fact(
                obj.clone(),
                Self::literal_zero_obj_for_abs_builtin(),
                line_file,
            )
            .into();
        Ok(self
            .try_verify_atomic_fact_as_builtin_rule_premise(&nonzero, builtin_state)?
            .map(|result| vec![result]))
    }

    pub(super) fn try_verify_power_addition_exponent_rule_one_direction(
        &mut self,
        combined_power: &Pow,
        product: &Mul,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let Obj::Add(add_exponent) = combined_power.exponent.as_ref() else {
            return Ok(None);
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
            let Some(mut subgoals) = self.try_verify_power_factor_matches_base_and_exponent(
                left_factor,
                combined_power.base.as_ref(),
                left_exp,
                line_file.clone(),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(mut right_factor_results) = self
                .try_verify_power_factor_matches_base_and_exponent(
                    right_factor,
                    combined_power.base.as_ref(),
                    right_exp,
                    line_file.clone(),
                    builtin_state,
                )?
            else {
                continue;
            };
            subgoals.append(&mut right_factor_results);

            let exponents_are_positive = combine_power_premise_groups([
                self.try_verify_obj_in_n_pos_for_power_builtin(
                    left_exp,
                    line_file.clone(),
                    builtin_state,
                )?,
                self.try_verify_obj_in_n_pos_for_power_builtin(
                    right_exp,
                    line_file.clone(),
                    builtin_state,
                )?,
            ]);
            if let Some(mut results) = exponents_are_positive {
                subgoals.append(&mut results);
                return Ok(Some(subgoals));
            }

            // Natural-exponent power law for complex bases:
            // `a^(m+n) = a^m * a^n`, including the cases m=0 or n=0.
            // Example: `forall a C, m, n N: a^m * a^n = a^(m+n)`.
            let natural_complex_results = combine_power_premise_groups([
                self.try_verify_obj_in_standard_set_for_power_builtin(
                    left_exp,
                    StandardSet::N,
                    line_file.clone(),
                    builtin_state,
                )?,
                self.try_verify_obj_in_standard_set_for_power_builtin(
                    right_exp,
                    StandardSet::N,
                    line_file.clone(),
                    builtin_state,
                )?,
                self.try_verify_obj_in_standard_set_for_power_builtin(
                    combined_power.base.as_ref(),
                    StandardSet::C,
                    line_file.clone(),
                    builtin_state,
                )?,
            ]);
            if let Some(mut results) = natural_complex_results {
                subgoals.append(&mut results);
                return Ok(Some(subgoals));
            }

            // Real-exponent addition law requires a positive real base.
            // Example: `forall a R+, m, n R: a^(m+n) = a^m * a^n`.
            let real_positive_results = combine_power_premise_groups([
                self.try_verify_obj_in_standard_set_for_power_builtin(
                    left_exp,
                    StandardSet::R,
                    line_file.clone(),
                    builtin_state,
                )?,
                self.try_verify_obj_in_standard_set_for_power_builtin(
                    right_exp,
                    StandardSet::R,
                    line_file.clone(),
                    builtin_state,
                )?,
                self.try_verify_obj_in_standard_set_for_power_builtin(
                    combined_power.base.as_ref(),
                    StandardSet::RPos,
                    line_file.clone(),
                    builtin_state,
                )?,
            ]);
            if let Some(mut results) = real_positive_results {
                subgoals.append(&mut results);
                return Ok(Some(subgoals));
            }

            // The remaining integer-exponent branch needs a nonzero base so negative
            // exponents do not accidentally justify undefined `0^(-n)`.
            // Example: `forall a R*, m, n Z: a^m * a^n = a^(m+n)`.
            let integer_nonzero_results = combine_power_premise_groups([
                self.try_verify_integer_exponent_for_power_builtin(
                    left_exp,
                    line_file.clone(),
                    builtin_state,
                )?,
                self.try_verify_integer_exponent_for_power_builtin(
                    right_exp,
                    line_file.clone(),
                    builtin_state,
                )?,
                self.try_verify_nonzero_for_power_builtin(
                    combined_power.base.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?,
            ]);
            if let Some(mut results) = integer_nonzero_results {
                subgoals.append(&mut results);
                return Ok(Some(subgoals));
            }

            // The carrier side condition is itself a disjunction of complete
            // sufficient branches. Consuming that QFF premise as a whole matters when,
            // for example, the context stores `m in N+ and n in N+` but neither leaf
            // was introduced independently.
            let base = combined_power.base.as_ref();
            let nonzero: AtomicFact = self
                .new_not_equal_fact(
                    base.clone(),
                    Self::literal_zero_obj_for_abs_builtin(),
                    line_file.clone(),
                )
                .into();
            let carrier_result = self.try_verify_builtin_rule_premise_alternatives(
                vec![
                    vec![
                        self.new_in_fact(
                            left_exp.clone(),
                            StandardSet::NPos.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            right_exp.clone(),
                            StandardSet::NPos.into(),
                            line_file.clone(),
                        )
                        .into(),
                    ],
                    vec![
                        self.new_in_fact(
                            left_exp.clone(),
                            StandardSet::N.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            right_exp.clone(),
                            StandardSet::N.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(base.clone(), StandardSet::C.into(), line_file.clone())
                            .into(),
                    ],
                    vec![
                        self.new_in_fact(
                            left_exp.clone(),
                            StandardSet::R.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            right_exp.clone(),
                            StandardSet::R.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(base.clone(), StandardSet::RPos.into(), line_file.clone())
                            .into(),
                    ],
                    vec![
                        self.new_in_fact(
                            left_exp.clone(),
                            StandardSet::Z.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            right_exp.clone(),
                            StandardSet::Z.into(),
                            line_file.clone(),
                        )
                        .into(),
                        nonzero,
                    ],
                ],
                line_file.clone(),
                builtin_state,
            )?;
            if let Some(carrier_result) = carrier_result {
                subgoals.push(carrier_result);
                return Ok(Some(subgoals));
            }
        }

        Ok(None)
    }

    pub fn try_verify_power_addition_exponent_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let subgoals = match (left, right) {
            (Obj::Pow(pow), Obj::Mul(product)) => self
                .try_verify_power_addition_exponent_rule_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    builtin_state,
                )?,
            (Obj::Mul(product), Obj::Pow(pow)) => self
                .try_verify_power_addition_exponent_rule_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    builtin_state,
                )?,
            _ => None,
        };
        if let Some(subgoals) = subgoals {
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(equal_fact, "equality: a^(m+n) = a^m * a^n for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base", subgoals)));
        }
        Ok(None)
    }

    pub(super) fn try_verify_power_of_power_rule_one_direction(
        &mut self,
        nested_power: &Pow,
        combined_power: &Pow,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let Obj::Pow(inner_power) = nested_power.base.as_ref() else {
            return Ok(None);
        };
        let Some(base_match) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(
                inner_power.base.as_ref(),
                combined_power.base.as_ref(),
                line_file.clone(),
            ),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let mut subgoals = vec![base_match];

        let multiplied_exponent: Obj = Mul::new(
            inner_power.exponent.as_ref().clone(),
            nested_power.exponent.as_ref().clone(),
        )
        .into();
        let Some(mut exponent_match_results) = self.try_verify_power_exponent_product_matches(
            inner_power.exponent.as_ref(),
            nested_power.exponent.as_ref(),
            &multiplied_exponent,
            combined_power.exponent.as_ref(),
            line_file.clone(),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        subgoals.append(&mut exponent_match_results);

        // Real-exponent power-of-power law requires a positive real base.
        // Example: `forall a R+, m, n R: (a^m)^n = a^(m*n)`.
        let positive_real_results = combine_power_premise_groups([
            self.try_verify_positive_real_base_for_power_builtin(
                combined_power.base.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_real_exponent_for_power_of_power(
                inner_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_real_exponent_for_power_of_power(
                nested_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
        ]);
        if let Some(mut results) = positive_real_results {
            subgoals.append(&mut results);
            return Ok(Some(subgoals));
        }

        // Power-of-power law for positive integer exponents:
        // `(a^m)^n = a^(m*n)`. Example: `forall a R, m, n N+: (a^m)^n = a^(m*n)`.
        let positive_exponent_results = combine_power_premise_groups([
            self.try_verify_obj_in_n_pos_for_power_builtin(
                inner_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_obj_in_n_pos_for_power_builtin(
                nested_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
        ]);
        if let Some(mut results) = positive_exponent_results {
            subgoals.append(&mut results);
            return Ok(Some(subgoals));
        }

        // Natural-exponent power-of-power law over complex bases, including zero exponents.
        // Example: `forall a C, m, n N: (a^m)^n = a^(m*n)`.
        let natural_complex_results = combine_power_premise_groups([
            self.try_verify_obj_in_standard_set_for_power_builtin(
                inner_power.exponent.as_ref(),
                StandardSet::N,
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_obj_in_standard_set_for_power_builtin(
                nested_power.exponent.as_ref(),
                StandardSet::N,
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_obj_in_standard_set_for_power_builtin(
                combined_power.base.as_ref(),
                StandardSet::C,
                line_file.clone(),
                builtin_state,
            )?,
        ]);
        if let Some(mut results) = natural_complex_results {
            subgoals.append(&mut results);
            return Ok(Some(subgoals));
        }

        // Integer-exponent power-of-power law needs a nonzero base so negative
        // exponents do not justify undefined powers of zero.
        // Example: `forall a R*, m, n Z: (a^m)^n = a^(m*n)`.
        let integer_nonzero_results = combine_power_premise_groups([
            self.try_verify_integer_exponent_for_power_builtin(
                inner_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_integer_exponent_for_power_builtin(
                nested_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_nonzero_for_power_builtin(
                combined_power.base.as_ref(),
                line_file.clone(),
                builtin_state,
            )?,
        ]);
        if let Some(mut results) = integer_nonzero_results {
            subgoals.append(&mut results);
            return Ok(Some(subgoals));
        }

        let inner_exp = inner_power.exponent.as_ref();
        let outer_exp = nested_power.exponent.as_ref();
        let base = combined_power.base.as_ref();
        let nonzero: AtomicFact = self
            .new_not_equal_fact(
                base.clone(),
                Self::literal_zero_obj_for_abs_builtin(),
                line_file.clone(),
            )
            .into();
        let carrier_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    self.new_in_fact(base.clone(), StandardSet::RPos.into(), line_file.clone())
                        .into(),
                    self.new_in_fact(inner_exp.clone(), StandardSet::R.into(), line_file.clone())
                        .into(),
                    self.new_in_fact(outer_exp.clone(), StandardSet::R.into(), line_file.clone())
                        .into(),
                ],
                vec![
                    self.new_in_fact(
                        inner_exp.clone(),
                        StandardSet::NPos.into(),
                        line_file.clone(),
                    )
                    .into(),
                    self.new_in_fact(
                        outer_exp.clone(),
                        StandardSet::NPos.into(),
                        line_file.clone(),
                    )
                    .into(),
                ],
                vec![
                    self.new_in_fact(inner_exp.clone(), StandardSet::N.into(), line_file.clone())
                        .into(),
                    self.new_in_fact(outer_exp.clone(), StandardSet::N.into(), line_file.clone())
                        .into(),
                    self.new_in_fact(base.clone(), StandardSet::C.into(), line_file.clone())
                        .into(),
                ],
                vec![
                    self.new_in_fact(inner_exp.clone(), StandardSet::Z.into(), line_file.clone())
                        .into(),
                    self.new_in_fact(outer_exp.clone(), StandardSet::Z.into(), line_file.clone())
                        .into(),
                    nonzero,
                ],
            ],
            line_file,
            builtin_state,
        )?;
        if let Some(carrier_result) = carrier_result {
            subgoals.push(carrier_result);
            return Ok(Some(subgoals));
        }
        Ok(None)
    }

    fn try_verify_power_exponent_product_matches(
        &mut self,
        left_factor: &Obj,
        right_factor: &Obj,
        product: &Obj,
        expected: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        if let Some(result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(product, expected, line_file.clone()),
            builtin_state,
        )? {
            return Ok(Some(vec![result]));
        }
        if !Self::obj_is_builtin_literal_one(expected) {
            return Ok(None);
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
            return Ok(None);
        };
        self.try_verify_nonzero_for_power_builtin(base, line_file, builtin_state)
    }

    // A power of a power can equal the bare base when the exponents multiply to one.
    // Example: for `a R+` and `b R*`, `(a^b)^(1 / b) = a`.
    fn try_verify_power_of_power_equals_base(
        &mut self,
        nested_power: &Pow,
        base: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        let combined_power = Pow::new(base.clone(), one);
        self.try_verify_power_of_power_rule_one_direction(
            nested_power,
            &combined_power,
            line_file,
            builtin_state,
        )
    }

    pub fn try_verify_power_of_power_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let subgoals = match (left, right) {
            (Obj::Pow(left_power), Obj::Pow(right_power)) => {
                if let Some(results) = self.try_verify_power_of_power_rule_one_direction(
                    left_power,
                    right_power,
                    line_file.clone(),
                    builtin_state,
                )? {
                    Some(results)
                } else {
                    self.try_verify_power_of_power_rule_one_direction(
                        right_power,
                        left_power,
                        line_file.clone(),
                        builtin_state,
                    )?
                }
            }
            (Obj::Pow(nested_power), base) => self.try_verify_power_of_power_equals_base(
                nested_power,
                base,
                line_file.clone(),
                builtin_state,
            )?,
            (base, Obj::Pow(nested_power)) => self.try_verify_power_of_power_equals_base(
                nested_power,
                base,
                line_file.clone(),
                builtin_state,
            )?,
            _ => None,
        };
        if let Some(subgoals) = subgoals {
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(equal_fact, "equality: (a^m)^n = a^(m*n) for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base", subgoals)));
        }
        Ok(None)
    }

    pub(super) fn try_verify_power_product_rule_one_direction(
        &mut self,
        combined_power: &Pow,
        product: &Mul,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let Obj::Mul(combined_base) = combined_power.base.as_ref() else {
            return Ok(None);
        };
        let exponent = combined_power.exponent.as_ref();
        let left_base = combined_base.left.as_ref();
        let right_base = combined_base.right.as_ref();

        // The first successful complete side-condition branch is retained.
        let side_condition_results = if let Some(results) = self
            .try_verify_obj_in_n_pos_for_power_builtin(exponent, line_file.clone(), builtin_state)?
        {
            Some(results)
        } else if let Some(results) = combine_power_premise_groups([
            self.try_verify_obj_in_standard_set_for_power_builtin(
                exponent,
                StandardSet::R,
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_positive_real_base_for_power_builtin(
                left_base,
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_positive_real_base_for_power_builtin(
                right_base,
                line_file.clone(),
                builtin_state,
            )?,
        ]) {
            Some(results)
        } else if let Some(results) = combine_power_premise_groups([
            self.try_verify_obj_in_standard_set_for_power_builtin(
                exponent,
                StandardSet::N,
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_obj_in_standard_set_for_power_builtin(
                left_base,
                StandardSet::C,
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_obj_in_standard_set_for_power_builtin(
                right_base,
                StandardSet::C,
                line_file.clone(),
                builtin_state,
            )?,
        ]) {
            Some(results)
        } else if let Some(results) = combine_power_premise_groups([
            self.try_verify_integer_exponent_for_power_builtin(
                exponent,
                line_file.clone(),
                builtin_state,
            )?,
            self.try_verify_nonzero_for_power_builtin(left_base, line_file.clone(), builtin_state)?,
            self.try_verify_nonzero_for_power_builtin(
                right_base,
                line_file.clone(),
                builtin_state,
            )?,
        ]) {
            Some(results)
        } else {
            let zero = Self::literal_zero_obj_for_abs_builtin();
            self.try_verify_builtin_rule_premise_alternatives(
                vec![
                    vec![self
                        .new_in_fact(
                            exponent.clone(),
                            StandardSet::NPos.into(),
                            line_file.clone(),
                        )
                        .into()],
                    vec![
                        self.new_in_fact(
                            exponent.clone(),
                            StandardSet::R.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            left_base.clone(),
                            StandardSet::RPos.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            right_base.clone(),
                            StandardSet::RPos.into(),
                            line_file.clone(),
                        )
                        .into(),
                    ],
                    vec![
                        self.new_in_fact(
                            exponent.clone(),
                            StandardSet::N.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            left_base.clone(),
                            StandardSet::C.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_in_fact(
                            right_base.clone(),
                            StandardSet::C.into(),
                            line_file.clone(),
                        )
                        .into(),
                    ],
                    vec![
                        self.new_in_fact(
                            exponent.clone(),
                            StandardSet::Z.into(),
                            line_file.clone(),
                        )
                        .into(),
                        self.new_not_equal_fact(left_base.clone(), zero.clone(), line_file.clone())
                            .into(),
                        self.new_not_equal_fact(right_base.clone(), zero, line_file.clone())
                            .into(),
                    ],
                ],
                line_file.clone(),
                builtin_state,
            )?
            .map(|result| vec![result])
        };
        let Some(mut side_condition_results) = side_condition_results else {
            return Ok(None);
        };

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
            let Some(mut left_results) = self.try_verify_power_factor_matches_base_and_exponent(
                left_factor,
                left_base,
                combined_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(mut right_results) = self.try_verify_power_factor_matches_base_and_exponent(
                right_factor,
                right_base,
                combined_power.exponent.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            else {
                continue;
            };
            side_condition_results.append(&mut left_results);
            side_condition_results.append(&mut right_results);
            return Ok(Some(side_condition_results));
        }

        Ok(None)
    }

    pub fn try_verify_power_product_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let subgoals = match (left, right) {
            (Obj::Pow(pow), Obj::Mul(product)) => self
                .try_verify_power_product_rule_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    builtin_state,
                )?,
            (Obj::Mul(product), Obj::Pow(pow)) => self
                .try_verify_power_product_rule_one_direction(
                    pow,
                    product,
                    line_file.clone(),
                    builtin_state,
                )?,
            _ => None,
        };
        if let Some(subgoals) = subgoals {
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(equal_fact, "equality: (a*b)^x = a^x * b^x for real x over positive real factors, n in N over complex bases, n in N+, or n in Z with nonzero bases", subgoals)));
        }
        Ok(None)
    }
}
