use super::*;

impl Runtime {
    // log_a(a^b) = b  (Litex `log(a, a^b) = b`; same base in log and in the power.)
    pub(crate) fn try_verify_log_identity_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };

        if let Obj::Pow(p) = log.arg.as_ref() {
            let base_ok = self.verify_objs_are_equal_in_equality_builtin(
                p.base.as_ref(),
                log.base.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if base_ok.is_true() {
                let exp_ok = self.verify_objs_are_equal_in_equality_builtin(
                    p.exponent.as_ref(),
                    other,
                    line_file.clone(),
                    verify_state,
                )?;
                if exp_ok.is_true() {
                    let mut subgoals = equality_builtin_match_subgoals(
                        p.base.as_ref(),
                        log.base.as_ref(),
                        base_ok,
                    );
                    subgoals.extend(equality_builtin_match_subgoals(
                        p.exponent.as_ref(),
                        other,
                        exp_ok,
                    ));
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        left,
                        right,
                        line_file,
                        "equality: log(a, a^b) = b",
                        subgoals,
                    )));
                }
            }
        }

        Ok(None)
    }

    // log_{a^b}(c) = log_a(c) / b  (Litex `log(a^b, c) = log(a, c) / b`; need b != 0 for a valid base.)
    pub(super) fn try_verify_log_base_power_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Pow(p) = log.base.as_ref() else {
            return Ok(None);
        };
        let inner_log: Obj = Log::new((*p.base).clone(), (*log.arg).clone()).into();
        let expected: Obj = Div::new(inner_log, (*p.exponent).clone()).into();
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            other,
            &expected,
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: log(a^b, c) = log(a, c) / b",
                subgoals,
            )));
        }
        Ok(None)
    }

    // log_a(x^b) = b * log_a(x)  (Litex `log(a, x^b) = b * log(a, x)`.)
    pub(super) fn try_verify_log_arg_power_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Pow(p) = log.arg.as_ref() else {
            return Ok(None);
        };
        let inner_log: Obj = Log::new((*log.base).clone(), (*p.base).clone()).into();
        let expected1: Obj = Mul::new((*p.exponent).clone(), inner_log.clone()).into();
        let expected2: Obj = Mul::new(inner_log, (*p.exponent).clone()).into();
        for expected in [expected1, expected2] {
            let inner = self.verify_objs_are_equal_in_equality_builtin(
                other,
                &expected,
                line_file.clone(),
                verify_state,
            )?;
            if inner.is_true() {
                let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x^b) = b * log(a, x)",
                    subgoals,
                )));
            }
        }
        Ok(None)
    }

    // log_a(x y) = log_a(x) + log_a(y)  (Litex `log(a, x*y) = log(a, x) + log(a, y)`.)
    pub(super) fn try_verify_log_product_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Mul(m) = log.arg.as_ref() else {
            return Ok(None);
        };
        let l1: Obj = Log::new((*log.base).clone(), (*m.left).clone()).into();
        let l2: Obj = Log::new((*log.base).clone(), (*m.right).clone()).into();
        let expected1: Obj = Add::new(l1.clone(), l2.clone()).into();
        let expected2: Obj = Add::new(l2, l1).into();
        for expected in [expected1, expected2] {
            let inner = self.verify_objs_are_equal_in_equality_builtin(
                other,
                &expected,
                line_file.clone(),
                verify_state,
            )?;
            if inner.is_true() {
                let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x*y) = log(a, x) + log(a, y)",
                    subgoals,
                )));
            }
        }
        Ok(None)
    }

    // log_a(x / y) = log_a(x) - log_a(y)  (Litex `log(a, x/y) = log(a, x) - log(a, y)`.)
    pub(super) fn try_verify_log_quotient_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Div(d) = log.arg.as_ref() else {
            return Ok(None);
        };
        let l1: Obj = Log::new((*log.base).clone(), (*d.left).clone()).into();
        let l2: Obj = Log::new((*log.base).clone(), (*d.right).clone()).into();
        let expected = Sub::new(l1, l2).into();
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            other,
            &expected,
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            let subgoals = equality_builtin_match_subgoals(other, &expected, inner);
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: log(a, x/y) = log(a, x) - log(a, y)",
                subgoals,
            )));
        }
        Ok(None)
    }

    // Algebraic log rules: log_{a^b}(c), log_a(x^b), log_a(x y), log_a(x / y) (see functions above).
    pub(crate) fn try_verify_log_algebra_identities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_log_base_power_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_log_arg_power_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_log_product_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        if let Some(done) =
            self.try_verify_log_quotient_rule(left, right, line_file.clone(), verify_state)?
        {
            return Ok(Some(done));
        }
        Ok(None)
    }

    // Reciprocal rule: log_a(1 / x) = -log_a(x).
    // Example: `forall a, x R_pos: a != 1 =>: log(a, 1 / x) = -log(a, x)`.
    pub(crate) fn try_verify_log_reciprocal_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Div(d) = log.arg.as_ref() else {
            return Ok(None);
        };
        let one = Self::literal_one_obj_for_log_builtin();
        let one_ok = self.verify_objs_are_equal_in_equality_builtin(
            d.left.as_ref(),
            &one,
            line_file.clone(),
            verify_state,
        )?;
        if !one_ok.is_true() {
            return Ok(None);
        }

        let inner_log: Obj = Log::new((*log.base).clone(), (*d.right).clone()).into();
        let expected1: Obj = Mul::new(
            Self::literal_neg_one_obj_for_log_builtin(),
            inner_log.clone(),
        )
        .into();
        let expected2: Obj = Mul::new(
            inner_log.clone(),
            Self::literal_neg_one_obj_for_log_builtin(),
        )
        .into();
        let expected3: Obj = Sub::new(Self::literal_zero_obj_for_abs_builtin(), inner_log).into();

        for expected in [expected1, expected2, expected3] {
            let ok = self.verify_objs_are_equal_in_equality_builtin(
                other,
                &expected,
                line_file.clone(),
                verify_state,
            )?;
            if ok.is_true() {
                let mut subgoals = equality_builtin_match_subgoals(d.left.as_ref(), &one, one_ok);
                subgoals.extend(equality_builtin_match_subgoals(other, &expected, ok));
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: log(a, 1/x) = -log(a, x)",
                    subgoals,
                )));
            }
        }

        Ok(None)
    }

    // Change of base: log_a(b) = log_c(b) / log_c(a).
    // Example: `forall a, b, c R_pos: a != 1, c != 1 =>: log(a, b) = log(c, b) / log(c, a)`.
    pub(crate) fn try_verify_log_change_of_base_rule(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log_ab, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let Obj::Div(d) = other else {
            return Ok(None);
        };
        let (Obj::Log(log_cb), Obj::Log(log_ca)) = (d.left.as_ref(), d.right.as_ref()) else {
            return Ok(None);
        };

        let base_ok = self.verify_objs_are_equal_in_equality_builtin(
            log_cb.base.as_ref(),
            log_ca.base.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !base_ok.is_true() {
            return Ok(None);
        }
        let arg_ok = self.verify_objs_are_equal_in_equality_builtin(
            log_cb.arg.as_ref(),
            log_ab.arg.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !arg_ok.is_true() {
            return Ok(None);
        }
        let inner_ok = self.verify_objs_are_equal_in_equality_builtin(
            log_ca.arg.as_ref(),
            log_ab.base.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if !inner_ok.is_true() {
            return Ok(None);
        }

        let mut subgoals =
            equality_builtin_match_subgoals(log_cb.base.as_ref(), log_ca.base.as_ref(), base_ok);
        subgoals.extend(equality_builtin_match_subgoals(
            log_cb.arg.as_ref(),
            log_ab.arg.as_ref(),
            arg_ok,
        ));
        subgoals.extend(equality_builtin_match_subgoals(
            log_ca.arg.as_ref(),
            log_ab.base.as_ref(),
            inner_ok,
        ));

        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            left,
            right,
            line_file,
            "equality: log(a, b) = log(c, b) / log(c, a)",
            subgoals,
        )))
    }

    // log_a(b) = c  iff  a^c = b  (Litex `log(a, b) = c`; reduces to proving `a^c = b`.)
    pub(crate) fn try_verify_log_equals_by_pow_inverse(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (log, other) = match (left, right) {
            (Obj::Log(l), o) => (l, o),
            (o, Obj::Log(l)) => (l, o),
            _ => return Ok(None),
        };
        let pow_obj: Obj = Pow::new((*log.base).clone(), other.clone()).into();
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            &pow_obj,
            log.arg.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: log(a, b) = c from a^c = b",
                vec![inner],
            )));
        }
        Ok(None)
    }

    // Exponential inverse in the other direction: a^c = b from known c = log_a(b).
    // Example: `forall a, b R_pos, c R: log(a, b) = c =>: a^c = b`.
    pub(crate) fn try_verify_pow_equals_by_known_log_inverse(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (pow, other) = match (left, right) {
            (Obj::Pow(p), o) => (p, o),
            (o, Obj::Pow(p)) => (p, o),
            _ => return Ok(None),
        };
        let expected_log: Obj = Log::new((*pow.base).clone(), other.clone()).into();
        let exponent_ok = self.verify_objs_are_equal_known_only(
            pow.exponent.as_ref(),
            &expected_log,
            line_file.clone(),
        );
        if !exponent_ok.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: a^c = b from c = log(a, b)".to_string(),
                vec![exponent_ok],
            )
            .into(),
        ))
    }
}
