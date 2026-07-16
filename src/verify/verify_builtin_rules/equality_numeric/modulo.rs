use super::*;

impl Runtime {
    /// `(x mod m) mod m = x mod m` when the nested `%` uses the same modulus as the outer `%`.
    ///
    /// Used to match residues after reducing summands: e.g. prove `X % Z = (X % Z) % Z` so
    /// `(X+Y)%Z = ((X%Z)+(Y%Z))%Z` can close via congruence.
    pub(crate) fn try_verify_mod_nested_same_modulus_absorption(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    outer.right.as_ref(),
                    inner.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    outer.right.as_ref(),
                    simple.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    inner.left.as_ref(),
                    simple.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: nested mod with same modulus absorbs inner mod",
            )));
        }
        Ok(None)
    }

    // a % m = (b % m) % m reduces to a % m = b % m (same m); the inner equality must be known-only.
    pub(crate) fn try_verify_mod_peel_nested_same_modulus(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                lm.right.as_ref(),
                rm.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let modulus = lm.right.as_ref();

        if let Obj::Mod(r_inner) = rm.left.as_ref() {
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    r_inner.right.as_ref(),
                    modulus,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                let lhs: Obj = Mod::new((*lm.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*r_inner.left).clone(), (*lm.right).clone()).into();
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        &lhs,
                        &rhs,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
                    )));
                }
            }
        }

        if let Obj::Mod(l_inner) = lm.left.as_ref() {
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    l_inner.right.as_ref(),
                    modulus,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                let lhs: Obj = Mod::new((*l_inner.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*rm.left).clone(), (*lm.right).clone()).into();
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        &lhs,
                        &rhs,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
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
    pub(crate) fn try_verify_mod_congruence_from_inner_binary(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                lm.right.as_ref(),
                rm.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let mut pair_ok = |a: &Obj, b: &Obj| -> Result<bool, RuntimeError> {
            let l: Obj = Mod::new(a.clone(), (*lm.right).clone()).into();
            let r: Obj = Mod::new(b.clone(), (*rm.right).clone()).into();
            Ok(self
                .verify_objs_are_equal_in_equality_builtin(&l, &r, line_file.clone(), verify_state)?
                .is_true())
        };
        let ok = match (lm.left.as_ref(), rm.left.as_ref()) {
            (Obj::Add(la), Obj::Add(ra)) => {
                pair_ok(la.left.as_ref(), ra.left.as_ref())?
                    && pair_ok(la.right.as_ref(), ra.right.as_ref())?
            }
            (Obj::Sub(ls), Obj::Sub(rs)) => {
                pair_ok(ls.left.as_ref(), rs.left.as_ref())?
                    && pair_ok(ls.right.as_ref(), rs.right.as_ref())?
            }
            (Obj::Mul(lx), Obj::Mul(rx)) => {
                pair_ok(lx.left.as_ref(), rx.left.as_ref())?
                    && pair_ok(lx.right.as_ref(), rx.right.as_ref())?
            }
            _ => return Ok(None),
        };
        if !ok {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: integer congruence — same modulus, residues for matching + / - / *",
        )))
    }

    // Negating an integer replaces its Euclidean residue by the complementary residue.
    // Example: for `n Z` and `k N_pos`, `(-n) % k = (k - n % k) % k`.
    pub(crate) fn try_verify_integer_mod_negation_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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

            let modulus_matches = self.verify_objs_are_equal_in_equality_builtin(
                negative_mod.right.as_ref(),
                complementary_mod.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !modulus_matches.is_true() {
                continue;
            }
            let complement_starts_at_modulus = self.verify_objs_are_equal_in_equality_builtin(
                complementary_sub.left.as_ref(),
                negative_mod.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !complement_starts_at_modulus.is_true() {
                continue;
            }
            let inner_modulus_matches = self.verify_objs_are_equal_in_equality_builtin(
                inner_remainder.right.as_ref(),
                negative_mod.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !inner_modulus_matches.is_true() {
                continue;
            }
            let dividend_matches = self.verify_objs_are_equal_in_equality_builtin(
                dividend,
                inner_remainder.left.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !dividend_matches.is_true() {
                continue;
            }

            let dividend_in_z: AtomicFact =
                InFact::new(dividend.clone(), StandardSet::Z.into(), line_file.clone()).into();
            let modulus_in_n_pos: AtomicFact = InFact::new(
                negative_mod.right.as_ref().clone(),
                StandardSet::NPos.into(),
                line_file.clone(),
            )
            .into();
            let dividend_result = self.verify_non_equational_known_then_builtin_rules_only(
                &dividend_in_z,
                verify_state,
            )?;
            let modulus_result = self.verify_non_equational_known_then_builtin_rules_only(
                &modulus_in_n_pos,
                verify_state,
            )?;
            if !dividend_result.is_true() || !modulus_result.is_true() {
                continue;
            }

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: (-n) % k = (k - n % k) % k for n in Z and k in N_pos",
                vec![
                    modulus_matches,
                    complement_starts_at_modulus,
                    inner_modulus_matches,
                    dividend_matches,
                    dividend_result,
                    modulus_result,
                ],
            )));
        }

        Ok(None)
    }

    // Reducing an integer before a natural power preserves its Euclidean residue.
    // Example: for `n Z`, `m N`, and `k N_pos`, `n^m % k = ((n % k)^m) % k`.
    pub(crate) fn try_verify_integer_mod_natural_power_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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

            let outer_modulus_matches = self.verify_objs_are_equal_in_equality_builtin(
                unreduced_mod.right.as_ref(),
                reduced_mod.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !outer_modulus_matches.is_true() {
                continue;
            }
            let inner_modulus_matches = self.verify_objs_are_equal_in_equality_builtin(
                unreduced_mod.right.as_ref(),
                inner_remainder.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !inner_modulus_matches.is_true() {
                continue;
            }
            let base_matches = self.verify_objs_are_equal_in_equality_builtin(
                unreduced_power.base.as_ref(),
                inner_remainder.left.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !base_matches.is_true() {
                continue;
            }
            let exponent_matches = self.verify_objs_are_equal_in_equality_builtin(
                unreduced_power.exponent.as_ref(),
                reduced_power.exponent.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !exponent_matches.is_true() {
                continue;
            }

            let base_in_z: AtomicFact = InFact::new(
                unreduced_power.base.as_ref().clone(),
                StandardSet::Z.into(),
                line_file.clone(),
            )
            .into();
            let exponent_in_n: AtomicFact = InFact::new(
                unreduced_power.exponent.as_ref().clone(),
                StandardSet::N.into(),
                line_file.clone(),
            )
            .into();
            let modulus_in_n_pos: AtomicFact = InFact::new(
                unreduced_mod.right.as_ref().clone(),
                StandardSet::NPos.into(),
                line_file.clone(),
            )
            .into();
            let base_result =
                self.verify_non_equational_known_then_builtin_rules_only(&base_in_z, verify_state)?;
            let exponent_result = self.verify_non_equational_known_then_builtin_rules_only(
                &exponent_in_n,
                verify_state,
            )?;
            let modulus_result = self.verify_non_equational_known_then_builtin_rules_only(
                &modulus_in_n_pos,
                verify_state,
            )?;
            if !base_result.is_true() || !exponent_result.is_true() || !modulus_result.is_true() {
                continue;
            }

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: n^m % k = ((n % k)^m) % k for n in Z, m in N, and k in N_pos",
                vec![
                    outer_modulus_matches,
                    inner_modulus_matches,
                    base_matches,
                    exponent_matches,
                    base_result,
                    exponent_result,
                    modulus_result,
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
