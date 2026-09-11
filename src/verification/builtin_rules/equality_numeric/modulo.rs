use super::*;

impl Runtime {
    /// `(x mod m) mod m = x mod m` when the nested `%` uses the same modulus as the outer `%`.
    ///
    /// Used to match residues after reducing summands: e.g. prove `X % Z = (X % Z) % Z` so
    /// `(X+Y)%Z = ((X%Z)+(Y%Z))%Z` can close via congruence.
    pub fn try_verify_mod_nested_same_modulus_absorption(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
            let Some(outer_inner_modulus) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    outer.right.as_ref(),
                    inner.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(outer_simple_modulus) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    outer.right.as_ref(),
                    simple.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(dividend_match) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    inner.left.as_ref(),
                    simple.left.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: nested mod with same modulus absorbs inner mod",
                vec![outer_inner_modulus, outer_simple_modulus, dividend_match],
            )));
        }
        Ok(None)
    }

    /// If `d` divides `m`, reducing modulo `m` before modulo `d` changes nothing.
    /// Example: `(a % 8) % 2 = a % 2` for `a in Z`.
    pub fn try_verify_mod_nested_divisible_modulus_absorption(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        for (nested_side, simple_side) in [(left, right), (right, left)] {
            let Obj::Mod(outer) = nested_side else {
                continue;
            };
            let Obj::Mod(inner) = outer.left.as_ref() else {
                continue;
            };
            let Obj::Mod(simple) = simple_side else {
                continue;
            };

            let outer_modulus_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    outer.right.as_ref(),
                    simple.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(outer_modulus_matches) = outer_modulus_matches else {
                continue;
            };
            let dividend_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    inner.left.as_ref(),
                    simple.left.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(dividend_matches) = dividend_matches else {
                continue;
            };

            let dividend_in_z: AtomicFact = self
                .new_in_fact(
                    inner.left.as_ref().clone(),
                    StandardSet::Z.into(),
                    line_file.clone(),
                )
                .into();
            let inner_modulus_in_n_pos: AtomicFact = self
                .new_in_fact(
                    inner.right.as_ref().clone(),
                    StandardSet::NPos.into(),
                    line_file.clone(),
                )
                .into();
            let outer_modulus_in_n_pos: AtomicFact = self
                .new_in_fact(
                    outer.right.as_ref().clone(),
                    StandardSet::NPos.into(),
                    line_file.clone(),
                )
                .into();
            let modulus_divisibility: AtomicFact = self
                .new_equal_fact(
                    Mod::new(inner.right.as_ref().clone(), outer.right.as_ref().clone()).into(),
                    Number::new("0".to_string()).into(),
                    line_file.clone(),
                )
                .into();

            let Some(carrier_results) = self.verify_builtin_rule_premises(
                &[
                    dividend_in_z,
                    inner_modulus_in_n_pos,
                    outer_modulus_in_n_pos,
                    modulus_divisibility,
                ],
                builtin_state,
            )?
            else {
                continue;
            };

            let mut subgoals = vec![outer_modulus_matches, dividend_matches];
            subgoals.extend(carrier_results);

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: nested mod absorbs an inner modulus divisible by the outer modulus",
                subgoals,
            )));
        }
        Ok(None)
    }

    // a % m = (b % m) % m reduces to a % m = b % m (same m); the inner equality must be known-only.
    pub fn try_verify_mod_peel_nested_same_modulus(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        let Some(modulus_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(lm.right.as_ref(), rm.right.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let modulus = lm.right.as_ref();

        if let Obj::Mod(r_inner) = rm.left.as_ref() {
            if let Some(inner_modulus_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(r_inner.right.as_ref(), modulus, line_file.clone()),
                builtin_state,
            )? {
                let lhs: Obj = Mod::new((*lm.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*r_inner.left).clone(), (*lm.right).clone()).into();
                if let Some(residue_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(&lhs, &rhs, line_file.clone()),
                    builtin_state,
                )? {
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        equal_fact,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
                        vec![modulus_result, inner_modulus_result, residue_result],
                    )));
                }
            }
        }

        if let Obj::Mod(l_inner) = lm.left.as_ref() {
            if let Some(inner_modulus_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(l_inner.right.as_ref(), modulus, line_file.clone()),
                builtin_state,
            )? {
                let lhs: Obj = Mod::new((*l_inner.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*rm.left).clone(), (*lm.right).clone()).into();
                if let Some(residue_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(&lhs, &rhs, line_file.clone()),
                    builtin_state,
                )? {
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        equal_fact,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
                        vec![modulus_result, inner_modulus_result, residue_result],
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
    pub fn try_verify_mod_congruence_from_inner_binary(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        let modulus_result = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(lm.right.as_ref(), rm.right.as_ref(), line_file.clone()),
            builtin_state,
        )?;
        let Some(modulus_result) = modulus_result else {
            return Ok(None);
        };

        let is_reduced_operand = |original: &Obj, reduced: &Obj, modulus: &Obj| {
            let Obj::Mod(remainder) = reduced else {
                return false;
            };
            objs_match_for_pattern(original, remainder.left.as_ref())
                && objs_match_for_pattern(modulus, remainder.right.as_ref())
        };
        let canonical_reduction_matches =
            |unreduced: &Obj, reduced: &Obj, modulus: &Obj| match (unreduced, reduced) {
                (Obj::Add(l), Obj::Add(r)) => {
                    is_reduced_operand(l.left.as_ref(), r.left.as_ref(), modulus)
                        && is_reduced_operand(l.right.as_ref(), r.right.as_ref(), modulus)
                }
                (Obj::Sub(l), Obj::Sub(r)) => {
                    is_reduced_operand(l.left.as_ref(), r.left.as_ref(), modulus)
                        && is_reduced_operand(l.right.as_ref(), r.right.as_ref(), modulus)
                }
                (Obj::Mul(l), Obj::Mul(r)) => {
                    is_reduced_operand(l.left.as_ref(), r.left.as_ref(), modulus)
                        && is_reduced_operand(l.right.as_ref(), r.right.as_ref(), modulus)
                }
                _ => false,
            };
        if canonical_reduction_matches(lm.left.as_ref(), rm.left.as_ref(), lm.right.as_ref())
            || canonical_reduction_matches(rm.left.as_ref(), lm.left.as_ref(), rm.right.as_ref())
        {
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: integer congruence — reduce matching + / - / * operands modulo m",
                equality_builtin_match_subgoals(
                    &self.new_equal_fact_from_refs(
                        lm.right.as_ref(),
                        rm.right.as_ref(),
                        line_file.clone(),
                    ),
                    modulus_result,
                ),
            )));
        }

        let modulus_fact =
            self.new_equal_fact_from_refs(lm.right.as_ref(), rm.right.as_ref(), line_file.clone());
        let mut pair_ok = |a: &Obj, b: &Obj| -> Result<Option<VerifyFactResult>, RuntimeError> {
            let l: Obj = Mod::new(a.clone(), (*lm.right).clone()).into();
            let r: Obj = Mod::new(b.clone(), (*rm.right).clone()).into();
            self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(&l, &r, line_file.clone()),
                builtin_state,
            )
        };
        let pairs = match (lm.left.as_ref(), rm.left.as_ref()) {
            (Obj::Add(left), Obj::Add(right)) => [
                (left.left.as_ref(), right.left.as_ref()),
                (left.right.as_ref(), right.right.as_ref()),
            ],
            (Obj::Sub(left), Obj::Sub(right)) => [
                (left.left.as_ref(), right.left.as_ref()),
                (left.right.as_ref(), right.right.as_ref()),
            ],
            (Obj::Mul(left), Obj::Mul(right)) => [
                (left.left.as_ref(), right.left.as_ref()),
                (left.right.as_ref(), right.right.as_ref()),
            ],
            _ => return Ok(None),
        };
        let mut subgoals = equality_builtin_match_subgoals(&modulus_fact, modulus_result);
        for (left, right) in pairs {
            let Some(pair_result) = pair_ok(left, right)? else {
                return Ok(None);
            };
            subgoals.push(pair_result);
        }
        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            equal_fact,
            "equality: integer congruence — same modulus, residues for matching + / - / *",
            subgoals,
        )))
    }

    // Negating an integer replaces its Euclidean residue by the complementary residue.
    // Example: for `n Z` and `k N+`, `(-n) % k = (k - n % k) % k`.
    pub fn try_verify_integer_mod_negation_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        for (negative_side, complementary_side) in [(left, right), (right, left)] {
            let Obj::Mod(negative_mod) = negative_side else {
                continue;
            };
            let Some(dividend) = negated_mod_dividend(negative_mod.left.as_ref()) else {
                continue;
            };
            let Obj::Mod(complementary_mod) = complementary_side else {
                continue;
            };
            let Obj::Sub(complementary_sub) = complementary_mod.left.as_ref() else {
                continue;
            };
            let Obj::Mod(inner_remainder) = complementary_sub.right.as_ref() else {
                continue;
            };

            let modulus_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    negative_mod.right.as_ref(),
                    complementary_mod.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(modulus_matches) = modulus_matches else {
                continue;
            };
            let complement_starts_at_modulus = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    complementary_sub.left.as_ref(),
                    negative_mod.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(complement_starts_at_modulus) = complement_starts_at_modulus else {
                continue;
            };
            let inner_modulus_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    inner_remainder.right.as_ref(),
                    negative_mod.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(inner_modulus_matches) = inner_modulus_matches else {
                continue;
            };
            let dividend_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    dividend,
                    inner_remainder.left.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(dividend_matches) = dividend_matches else {
                continue;
            };

            let dividend_in_z: AtomicFact = self
                .new_in_fact(dividend.clone(), StandardSet::Z.into(), line_file.clone())
                .into();
            let modulus_in_n_pos: AtomicFact = self
                .new_in_fact(
                    negative_mod.right.as_ref().clone(),
                    StandardSet::NPos.into(),
                    line_file.clone(),
                )
                .into();
            let Some(carrier_results) = self
                .verify_builtin_rule_premises(&[dividend_in_z, modulus_in_n_pos], builtin_state)?
            else {
                continue;
            };

            let mut subgoals = vec![
                modulus_matches,
                complement_starts_at_modulus,
                inner_modulus_matches,
                dividend_matches,
            ];
            subgoals.extend(carrier_results);

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: (-n) % k = (k - n % k) % k for n in Z and k in N+",
                subgoals,
            )));
        }

        Ok(None)
    }

    // Reducing an integer before a natural power preserves its Euclidean residue.
    // Example: for `n Z`, `m N`, and `k N+`, `n^m % k = ((n % k)^m) % k`.
    pub fn try_verify_integer_mod_natural_power_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        for (unreduced_side, reduced_side) in [(left, right), (right, left)] {
            let Obj::Mod(unreduced_mod) = unreduced_side else {
                continue;
            };
            let Obj::Pow(unreduced_power) = unreduced_mod.left.as_ref() else {
                continue;
            };
            let Obj::Mod(reduced_mod) = reduced_side else {
                continue;
            };
            let Obj::Pow(reduced_power) = reduced_mod.left.as_ref() else {
                continue;
            };
            let Obj::Mod(inner_remainder) = reduced_power.base.as_ref() else {
                continue;
            };

            let outer_modulus_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    unreduced_mod.right.as_ref(),
                    reduced_mod.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(outer_modulus_matches) = outer_modulus_matches else {
                continue;
            };
            let inner_modulus_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    unreduced_mod.right.as_ref(),
                    inner_remainder.right.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(inner_modulus_matches) = inner_modulus_matches else {
                continue;
            };
            let base_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    unreduced_power.base.as_ref(),
                    inner_remainder.left.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(base_matches) = base_matches else {
                continue;
            };
            let exponent_matches = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    unreduced_power.exponent.as_ref(),
                    reduced_power.exponent.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?;
            let Some(exponent_matches) = exponent_matches else {
                continue;
            };

            let base_in_z: AtomicFact = self
                .new_in_fact(
                    unreduced_power.base.as_ref().clone(),
                    StandardSet::Z.into(),
                    line_file.clone(),
                )
                .into();
            let exponent_in_n: AtomicFact = self
                .new_in_fact(
                    unreduced_power.exponent.as_ref().clone(),
                    StandardSet::N.into(),
                    line_file.clone(),
                )
                .into();
            let modulus_in_n_pos: AtomicFact = self
                .new_in_fact(
                    unreduced_mod.right.as_ref().clone(),
                    StandardSet::NPos.into(),
                    line_file.clone(),
                )
                .into();
            let exponent_in_n_pos: AtomicFact = self
                .new_in_fact(
                    unreduced_power.exponent.as_ref().clone(),
                    StandardSet::NPos.into(),
                    line_file.clone(),
                )
                .into();
            let Some(carrier_result) = self.try_verify_builtin_rule_premise_alternatives(
                vec![
                    vec![base_in_z.clone(), exponent_in_n, modulus_in_n_pos.clone()],
                    vec![base_in_z, exponent_in_n_pos, modulus_in_n_pos],
                ],
                line_file.clone(),
                builtin_state,
            )?
            else {
                continue;
            };

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: n^m % k = ((n % k)^m) % k for n in Z, m in N, and k in N+",
                vec![
                    outer_modulus_matches,
                    inner_modulus_matches,
                    base_matches,
                    exponent_matches,
                    carrier_result,
                ],
            )));
        }

        Ok(None)
    }
}

fn negated_mod_dividend(obj: &Obj) -> Option<&Obj> {
    let Obj::Mul(mul) = obj else {
        return None;
    };
    if Runtime::obj_is_builtin_literal_neg_one(mul.left.as_ref()) {
        return Some(mul.right.as_ref());
    }
    if Runtime::obj_is_builtin_literal_neg_one(mul.right.as_ref()) {
        return Some(mul.left.as_ref());
    }
    None
}
