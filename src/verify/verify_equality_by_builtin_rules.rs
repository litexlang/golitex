use crate::prelude::*;
use crate::verify::verify_builtin_rules::{
    compare_normalized_number_str_to_zero, NumberCompareResult,
};
use crate::verify::verify_number_in_standard_set::is_integer_after_simplification;
use std::collections::HashMap;
use std::rc::Rc;

pub fn verify_equality_by_they_are_the_same(left: &Obj, right: &Obj) -> bool {
    if left.to_string() == right.to_string() {
        return true;
    }
    false
}

fn factual_equal_success_by_builtin_reason(
    left: &Obj,
    right: &Obj,
    line_file: LineFile,
    reason: &str,
) -> StmtResult {
    StmtResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            EqualFact::new(left.clone(), right.clone(), line_file).into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

impl Runtime {
    // Instantiate family `equal_to` on one or both sides, then full `verify_objs_are_equal` on the expanded pair.
    fn try_verify_objs_equal_by_expanding_family(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let (Obj::FamilyObj(fl), Obj::FamilyObj(fr)) = (left, right) {
            if let (Ok(el), Ok(er)) = (
                self.instantiate_family_member_set(fl),
                self.instantiate_family_member_set(fr),
            ) {
                let r = self.verify_objs_are_equal(&el, &er, line_file.clone(), verify_state)?;
                if r.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: expand family definition (substitute parameters into equal_to)",
                    )));
                }
            }
        }
        if let Obj::FamilyObj(f) = left {
            if let Ok(expanded) = self.instantiate_family_member_set(f) {
                let r =
                    self.verify_objs_are_equal(&expanded, right, line_file.clone(), verify_state)?;
                if r.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: expand family definition (substitute parameters into equal_to)",
                    )));
                }
            }
        }
        if let Obj::FamilyObj(f) = right {
            if let Ok(expanded) = self.instantiate_family_member_set(f) {
                let r =
                    self.verify_objs_are_equal(left, &expanded, line_file.clone(), verify_state)?;
                if r.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: expand family definition (substitute parameters into equal_to)",
                    )));
                }
            }
        }
        Ok(None)
    }

    fn obj_is_builtin_literal_zero(obj: &Obj) -> bool {
        match obj {
            Obj::Number(n) => matches!(
                compare_normalized_number_str_to_zero(&n.normalized_value),
                NumberCompareResult::Equal
            ),
            _ => false,
        }
    }

    // Literal 0 vs `x - y`: verify the equality if `x = y` holds via the full equality pipeline.
    fn try_verify_zero_equals_subtraction_implies_equal_operands(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
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

        let inner = self.verify_objs_are_equal(x, y, line_file.clone(), verify_state)?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: 0 = x - y with x = y (known or builtin)",
            )));
        }
        Ok(None)
    }

    // 0 = a^n when n is a literal integer > 0 (avoids 0^0 /0^negative), from a = 0.
    fn try_verify_zero_equals_pow_from_base_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
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
        let inner = self.verify_objs_are_equal(base, zero_side, line_file.clone(), verify_state)?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: 0 = a^n from a = 0, n positive integer literal",
            )));
        }
        Ok(None)
    }

    // log_a(a^b) = b  (Litex `log(a, a^b) = b`; same base in log and in the power.)
    fn try_verify_log_identity_equalities(
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
            let base_ok = self.verify_objs_are_equal(
                p.base.as_ref(),
                log.base.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if base_ok.is_true() {
                let exp_ok = self.verify_objs_are_equal(
                    p.exponent.as_ref(),
                    other,
                    line_file.clone(),
                    verify_state,
                )?;
                if exp_ok.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: log(a, a^b) = b",
                    )));
                }
            }
        }

        Ok(None)
    }

    // log_{a^b}(c) = log_a(c) / b  (Litex `log(a^b, c) = log(a, c) / b`; need b != 0 for a valid base.)
    fn try_verify_log_base_power_rule(
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
        let inner =
            self.verify_objs_are_equal(other, &expected, line_file.clone(), verify_state)?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: log(a^b, c) = log(a, c) / b",
            )));
        }
        Ok(None)
    }

    // log_a(x^b) = b * log_a(x)  (Litex `log(a, x^b) = b * log(a, x)`.)
    fn try_verify_log_arg_power_rule(
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
            let inner =
                self.verify_objs_are_equal(other, &expected, line_file.clone(), verify_state)?;
            if inner.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x^b) = b * log(a, x)",
                )));
            }
        }
        Ok(None)
    }

    // log_a(x y) = log_a(x) + log_a(y)  (Litex `log(a, x*y) = log(a, x) + log(a, y)`.)
    fn try_verify_log_product_rule(
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
            let inner =
                self.verify_objs_are_equal(other, &expected, line_file.clone(), verify_state)?;
            if inner.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: log(a, x*y) = log(a, x) + log(a, y)",
                )));
            }
        }
        Ok(None)
    }

    // log_a(x / y) = log_a(x) - log_a(y)  (Litex `log(a, x/y) = log(a, x) - log(a, y)`.)
    fn try_verify_log_quotient_rule(
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
        let inner =
            self.verify_objs_are_equal(other, &expected, line_file.clone(), verify_state)?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: log(a, x/y) = log(a, x) - log(a, y)",
            )));
        }
        Ok(None)
    }

    // Algebraic log rules: log_{a^b}(c), log_a(x^b), log_a(x y), log_a(x / y) (see functions above).
    fn try_verify_log_algebra_identities(
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

    // log_a(b) = c  iff  a^c = b  (Litex `log(a, b) = c`; reduces to proving `a^c = b`.)
    fn try_verify_log_equals_by_pow_inverse(
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
        let inner = self.verify_objs_are_equal(
            &pow_obj,
            log.arg.as_ref(),
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: log(a, b) = c from a^c = b",
            )));
        }
        Ok(None)
    }

    // sum(i,a,e+1,F) = sum(i,a,e,F) + tail with i bound to outer end (same i,a,F; one binary + on the other side).
    fn try_finish_sum_peel_equality(
        &mut self,
        outer: &SumObj,
        inner: &SumObj,
        actual_tail: &Obj,
        display_left: &Obj,
        display_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        if outer.param != inner.param {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal(
                outer.start.as_ref(),
                inner.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal(
                outer.body.as_ref(),
                inner.body.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let end_plus_one: Obj = Add::new((*inner.end).clone(), one.clone()).into();
        if !self
            .verify_objs_are_equal(
                outer.end.as_ref(),
                &end_plus_one,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let mut m = HashMap::new();
        m.insert(outer.param.clone(), (*outer.end).clone());
        let Ok(expected_tail) = self.inst_obj(outer.body.as_ref(), &m, ParamObjType::Sum) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal(actual_tail, &expected_tail, line_file.clone(), verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            display_left,
            display_right,
            line_file,
            "equality: sum upper +1 = inner sum + term at new index",
        )))
    }

    fn try_verify_sum_peel_last_term_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Sum(lsum) = left {
            if let Obj::Add(add) = right {
                for (sum_side, tail_side) in [
                    (add.left.as_ref(), add.right.as_ref()),
                    (add.right.as_ref(), add.left.as_ref()),
                ] {
                    if let Obj::Sum(rsum) = sum_side {
                        if let Some(done) = self.try_finish_sum_peel_equality(
                            lsum,
                            rsum,
                            tail_side,
                            left,
                            right,
                            line_file.clone(),
                            verify_state,
                        )? {
                            return Ok(Some(done));
                        }
                    }
                }
            }
        }
        if let Obj::Sum(rsum) = right {
            if let Obj::Add(add) = left {
                for (sum_side, tail_side) in [
                    (add.left.as_ref(), add.right.as_ref()),
                    (add.right.as_ref(), add.left.as_ref()),
                ] {
                    if let Obj::Sum(lsum) = sum_side {
                        if let Some(done) = self.try_finish_sum_peel_equality(
                            rsum,
                            lsum,
                            tail_side,
                            left,
                            right,
                            line_file.clone(),
                            verify_state,
                        )? {
                            return Ok(Some(done));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    // sum(i,a,b,F+G) = sum(i,a,b,F) + sum(i,a,b,G); other side is one binary + with two sums (order either way).
    fn try_match_sum_additivity_one_direction(
        &mut self,
        outer: &SumObj,
        other: &Obj,
        display_left: &Obj,
        display_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Add(body_add) = outer.body.as_ref() else {
            return Ok(None);
        };
        let Obj::Add(outer_add) = other else {
            return Ok(None);
        };
        for (x_side, y_side) in [
            (outer_add.left.as_ref(), outer_add.right.as_ref()),
            (outer_add.right.as_ref(), outer_add.left.as_ref()),
        ] {
            if let (Obj::Sum(sx), Obj::Sum(sy)) = (x_side, y_side) {
                if outer.param != sx.param || outer.param != sy.param {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.start.as_ref(),
                        sx.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.start.as_ref(),
                        sy.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.end.as_ref(),
                        sx.end.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.end.as_ref(),
                        sy.end.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let fl = body_add.left.as_ref();
                let fr = body_add.right.as_ref();
                let match_fg = self
                    .verify_objs_are_equal(fl, sx.body.as_ref(), line_file.clone(), verify_state)?
                    .is_true()
                    && self
                        .verify_objs_are_equal(fr, sy.body.as_ref(), line_file.clone(), verify_state)?
                        .is_true();
                let match_gf = self
                    .verify_objs_are_equal(fl, sy.body.as_ref(), line_file.clone(), verify_state)?
                    .is_true()
                    && self
                        .verify_objs_are_equal(fr, sx.body.as_ref(), line_file.clone(), verify_state)?
                        .is_true();
                if match_fg || match_gf {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        display_left,
                        display_right,
                        line_file,
                        "equality: sum(summand + summand) = sum + sum same bounds",
                    )));
                }
            }
        }
        Ok(None)
    }

    fn try_verify_sum_additivity_same_bounds_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Sum(lsum) = left {
            if let Some(done) = self.try_match_sum_additivity_one_direction(
                lsum,
                right,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        if let Obj::Sum(rsum) = right {
            if let Some(done) = self.try_match_sum_additivity_one_direction(
                rsum,
                left,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    // sum(i,a,a,F) = inst(F, { i ↦ a }) when start and end are equal.
    fn try_match_sum_single_index_interval_one_direction(
        &mut self,
        s: &SumObj,
        other: &Obj,
        display_left: &Obj,
        display_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !self
            .verify_objs_are_equal(
                s.start.as_ref(),
                s.end.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let mut m = HashMap::new();
        m.insert(s.param.clone(), (*s.start).clone());
        let Ok(inst_body) = self.inst_obj(s.body.as_ref(), &m, ParamObjType::Sum) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal(&inst_body, other, line_file.clone(), verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            display_left,
            display_right,
            line_file,
            "equality: sum with start = end is single instantiated summand",
        )))
    }

    fn try_verify_sum_single_index_interval_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Sum(lsum) = left {
            if let Some(done) = self.try_match_sum_single_index_interval_one_direction(
                lsum,
                right,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        if let Obj::Sum(rsum) = right {
            if let Some(done) = self.try_match_sum_single_index_interval_one_direction(
                rsum,
                left,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    // sum(i,a,b,F) = sum(i,a,k,F) + sum(i,k+1,b,F): same i,a,b,F; first segment ends at k, second starts at k+1.
    fn try_verify_sum_split_adjacent_segments_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        if let Obj::Sum(lsum) = left {
            if let Obj::Add(add) = right {
                for (s1_side, s2_side) in [
                    (add.left.as_ref(), add.right.as_ref()),
                    (add.right.as_ref(), add.left.as_ref()),
                ] {
                    if let (Obj::Sum(s1), Obj::Sum(s2)) = (s1_side, s2_side) {
                        if lsum.param != s1.param || lsum.param != s2.param {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lsum.start.as_ref(),
                                s1.start.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lsum.end.as_ref(),
                                s2.end.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lsum.body.as_ref(),
                                s1.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lsum.body.as_ref(),
                                s2.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*s1.end).clone(), one.clone()).into();
                        if !self
                            .verify_objs_are_equal(
                                &first_end_plus_one,
                                s2.start.as_ref(),
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
                            "equality: sum splits into adjacent segments (end+1 = next start)",
                        )));
                    }
                }
            }
        }
        if let Obj::Sum(rsum) = right {
            if let Obj::Add(add) = left {
                for (s1_side, s2_side) in [
                    (add.left.as_ref(), add.right.as_ref()),
                    (add.right.as_ref(), add.left.as_ref()),
                ] {
                    if let (Obj::Sum(s1), Obj::Sum(s2)) = (s1_side, s2_side) {
                        if rsum.param != s1.param || rsum.param != s2.param {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rsum.start.as_ref(),
                                s1.start.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rsum.end.as_ref(),
                                s2.end.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rsum.body.as_ref(),
                                s1.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rsum.body.as_ref(),
                                s2.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*s1.end).clone(), one.clone()).into();
                        if !self
                            .verify_objs_are_equal(
                                &first_end_plus_one,
                                s2.start.as_ref(),
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
                            "equality: sum splits into adjacent segments (end+1 = next start)",
                        )));
                    }
                }
            }
        }
        Ok(None)
    }

    // product(i,a,e+1,F) = product(i,a,e,F) * tail with i bound to outer end (same i,a,F; one binary * on the other side).
    fn try_finish_product_peel_equality(
        &mut self,
        outer: &ProductObj,
        inner: &ProductObj,
        actual_tail: &Obj,
        display_left: &Obj,
        display_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        if outer.param != inner.param {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal(
                outer.start.as_ref(),
                inner.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal(
                outer.body.as_ref(),
                inner.body.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let end_plus_one: Obj = Add::new((*inner.end).clone(), one.clone()).into();
        if !self
            .verify_objs_are_equal(
                outer.end.as_ref(),
                &end_plus_one,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let mut m = HashMap::new();
        m.insert(outer.param.clone(), (*outer.end).clone());
        let Ok(expected_tail) = self.inst_obj(outer.body.as_ref(), &m, ParamObjType::Product)
        else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal(actual_tail, &expected_tail, line_file.clone(), verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            display_left,
            display_right,
            line_file,
            "equality: product upper +1 = inner product * factor at new index",
        )))
    }

    fn try_verify_product_peel_last_term_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Product(lprod) = left {
            if let Obj::Mul(mul) = right {
                for (prod_side, tail_side) in [
                    (mul.left.as_ref(), mul.right.as_ref()),
                    (mul.right.as_ref(), mul.left.as_ref()),
                ] {
                    if let Obj::Product(rprod) = prod_side {
                        if let Some(done) = self.try_finish_product_peel_equality(
                            lprod,
                            rprod,
                            tail_side,
                            left,
                            right,
                            line_file.clone(),
                            verify_state,
                        )? {
                            return Ok(Some(done));
                        }
                    }
                }
            }
        }
        if let Obj::Product(rprod) = right {
            if let Obj::Mul(mul) = left {
                for (prod_side, tail_side) in [
                    (mul.left.as_ref(), mul.right.as_ref()),
                    (mul.right.as_ref(), mul.left.as_ref()),
                ] {
                    if let Obj::Product(lprod) = prod_side {
                        if let Some(done) = self.try_finish_product_peel_equality(
                            rprod,
                            lprod,
                            tail_side,
                            left,
                            right,
                            line_file.clone(),
                            verify_state,
                        )? {
                            return Ok(Some(done));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    // product(i,a,b,F*G) = product(i,a,b,F) * product(i,a,b,G); other side is one binary * with two products (order either way).
    fn try_match_product_multiplicativity_one_direction(
        &mut self,
        outer: &ProductObj,
        other: &Obj,
        display_left: &Obj,
        display_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Mul(body_mul) = outer.body.as_ref() else {
            return Ok(None);
        };
        let Obj::Mul(outer_mul) = other else {
            return Ok(None);
        };
        for (x_side, y_side) in [
            (outer_mul.left.as_ref(), outer_mul.right.as_ref()),
            (outer_mul.right.as_ref(), outer_mul.left.as_ref()),
        ] {
            if let (Obj::Product(px), Obj::Product(py)) = (x_side, y_side) {
                if outer.param != px.param || outer.param != py.param {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.start.as_ref(),
                        px.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.start.as_ref(),
                        py.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.end.as_ref(),
                        px.end.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal(
                        outer.end.as_ref(),
                        py.end.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let fl = body_mul.left.as_ref();
                let fr = body_mul.right.as_ref();
                let match_fg = self
                    .verify_objs_are_equal(fl, px.body.as_ref(), line_file.clone(), verify_state)?
                    .is_true()
                    && self
                        .verify_objs_are_equal(fr, py.body.as_ref(), line_file.clone(), verify_state)?
                        .is_true();
                let match_gf = self
                    .verify_objs_are_equal(fl, py.body.as_ref(), line_file.clone(), verify_state)?
                    .is_true()
                    && self
                        .verify_objs_are_equal(fr, px.body.as_ref(), line_file.clone(), verify_state)?
                        .is_true();
                if match_fg || match_gf {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        display_left,
                        display_right,
                        line_file,
                        "equality: product(factor * factor) = product * product same bounds",
                    )));
                }
            }
        }
        Ok(None)
    }

    fn try_verify_product_multiplicativity_same_bounds_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Product(lprod) = left {
            if let Some(done) = self.try_match_product_multiplicativity_one_direction(
                lprod,
                right,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        if let Obj::Product(rprod) = right {
            if let Some(done) = self.try_match_product_multiplicativity_one_direction(
                rprod,
                left,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    // product(i,a,a,F) = inst(F, { i ↦ a }) when start and end are equal.
    fn try_match_product_single_index_interval_one_direction(
        &mut self,
        s: &ProductObj,
        other: &Obj,
        display_left: &Obj,
        display_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !self
            .verify_objs_are_equal(
                s.start.as_ref(),
                s.end.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let mut m = HashMap::new();
        m.insert(s.param.clone(), (*s.start).clone());
        let Ok(inst_body) = self.inst_obj(s.body.as_ref(), &m, ParamObjType::Product) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal(&inst_body, other, line_file.clone(), verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            display_left,
            display_right,
            line_file,
            "equality: product with start = end is single instantiated factor",
        )))
    }

    fn try_verify_product_single_index_interval_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Product(lprod) = left {
            if let Some(done) = self.try_match_product_single_index_interval_one_direction(
                lprod,
                right,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        if let Obj::Product(rprod) = right {
            if let Some(done) = self.try_match_product_single_index_interval_one_direction(
                rprod,
                left,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    // product(i,a,b,F) = product(i,a,k,F) * product(i,k+1,b,F): same i,a,b,F; first segment ends at k, second starts at k+1.
    fn try_verify_product_split_adjacent_segments_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        if let Obj::Product(lprod) = left {
            if let Obj::Mul(mul) = right {
                for (p1_side, p2_side) in [
                    (mul.left.as_ref(), mul.right.as_ref()),
                    (mul.right.as_ref(), mul.left.as_ref()),
                ] {
                    if let (Obj::Product(p1), Obj::Product(p2)) = (p1_side, p2_side) {
                        if lprod.param != p1.param || lprod.param != p2.param {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lprod.start.as_ref(),
                                p1.start.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lprod.end.as_ref(),
                                p2.end.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lprod.body.as_ref(),
                                p1.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                lprod.body.as_ref(),
                                p2.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*p1.end).clone(), one.clone()).into();
                        if !self
                            .verify_objs_are_equal(
                                &first_end_plus_one,
                                p2.start.as_ref(),
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
                            "equality: product splits into adjacent segments (end+1 = next start)",
                        )));
                    }
                }
            }
        }
        if let Obj::Product(rprod) = right {
            if let Obj::Mul(mul) = left {
                for (p1_side, p2_side) in [
                    (mul.left.as_ref(), mul.right.as_ref()),
                    (mul.right.as_ref(), mul.left.as_ref()),
                ] {
                    if let (Obj::Product(p1), Obj::Product(p2)) = (p1_side, p2_side) {
                        if rprod.param != p1.param || rprod.param != p2.param {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rprod.start.as_ref(),
                                p1.start.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rprod.end.as_ref(),
                                p2.end.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rprod.body.as_ref(),
                                p1.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        if !self
                            .verify_objs_are_equal(
                                rprod.body.as_ref(),
                                p2.body.as_ref(),
                                line_file.clone(),
                                verify_state,
                            )?
                            .is_true()
                        {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*p1.end).clone(), one.clone()).into();
                        if !self
                            .verify_objs_are_equal(
                                &first_end_plus_one,
                                p2.start.as_ref(),
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
                            "equality: product splits into adjacent segments (end+1 = next start)",
                        )));
                    }
                }
            }
        }
        Ok(None)
    }

    pub fn verify_equality_by_builtin_rules(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(done) = self.try_verify_objs_equal_by_expanding_family(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_equals_subtraction_implies_equal_operands(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_zero_equals_pow_from_base_zero(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_identity_equalities(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_algebra_identities(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) =
            self.try_verify_log_equals_by_pow_inverse(left, right, line_file.clone(), verify_state)?
        {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_peel_last_term_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_additivity_same_bounds_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_single_index_interval_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_split_adjacent_segments_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_product_peel_last_term_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_product_multiplicativity_same_bounds_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_product_single_index_interval_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_product_split_adjacent_segments_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        let (result, calculated_left, calculated_right) = self
            .verify_equality_by_they_are_the_same_and_calculation(
                left,
                right,
                line_file.clone(),
                verify_state,
            )?;
        if result.is_true() {
            return Ok(result);
        }

        if objs_equal_by_rational_expression_evaluation(&calculated_left, &calculated_right) {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left.clone(), right.clone(), line_file).into(),
                    "calculation and rational expression simplification".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        if let (Obj::FnSet(left_fn_set), Obj::FnSet(right_fn_set)) = (left, right) {
            return self.verify_fn_set_with_params_equality_by_builtin_rules(
                left_fn_set,
                right_fn_set,
                line_file,
                verify_state,
            );
        }

        Ok((StmtUnknown::new()).into())
    }
}

impl Runtime {
    fn try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (result, _, _) = self.verify_equality_by_they_are_the_same_and_calculation(
            left,
            right,
            line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(Some(result));
        }
        if let Some(shape_result) =
            self.try_verify_equal_by_same_shape_and_known_equality_args(left, right, line_file)
        {
            if shape_result.is_true() {
                return Ok(Some(shape_result));
            }
        }
        Ok(None)
    }

    pub fn try_verify_equality_with_known_equalities_by_builtin_rules_only(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
        known_objs_equal_to_left: Option<&Rc<Vec<Obj>>>,
        known_objs_equal_to_right: Option<&Rc<Vec<Obj>>>,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        match (known_objs_equal_to_left, known_objs_equal_to_right) {
            (None, None) => Ok(None),
            (Some(known_objs_equal_to_left), None) => {
                for obj in known_objs_equal_to_left.iter() {
                    if let Some(result) = self
                        .try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
                            obj,
                            right,
                            line_file.clone(),
                            verify_state,
                        )?
                    {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (None, Some(known_objs_equal_to_right)) => {
                for obj in known_objs_equal_to_right.iter() {
                    if let Some(result) = self
                        .try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
                            left,
                            obj,
                            line_file.clone(),
                            verify_state,
                        )?
                    {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (Some(known_objs_equal_to_left), Some(known_objs_equal_to_right)) => {
                for obj1 in known_objs_equal_to_left.iter() {
                    for obj2 in known_objs_equal_to_right.iter() {
                        if let Some(result) = self
                            .try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
                                obj1,
                                obj2,
                                line_file.clone(),
                                verify_state,
                            )?
                        {
                            return Ok(Some(result));
                        }
                    }
                }
                Ok(None)
            }
        }
    }

    pub fn objs_have_same_known_equality_rc_in_some_env(&self, left: &Obj, right: &Obj) -> bool {
        let left_key: ObjString = left.to_string();
        let right_key: ObjString = right.to_string();
        for env in self.iter_environments_from_top() {
            let left_entry = env.known_equality.get(&left_key);
            let right_entry = env.known_equality.get(&right_key);
            if let (Some((_, left_rc)), Some((_, right_rc))) = (left_entry, right_entry) {
                if Rc::ptr_eq(left_rc, right_rc) {
                    return true;
                }
            }
        }
        false
    }

    fn arg_pairs_share_known_equality_class(&self, pairs: &[(&Obj, &Obj)]) -> bool {
        pairs
            .iter()
            .all(|(a, b)| self.objs_have_same_known_equality_rc_in_some_env(a, b))
    }

    fn boxed_obj_vecs_share_known_equality_class(
        &self,
        left: &[Box<Obj>],
        right: &[Box<Obj>],
    ) -> bool {
        if left.len() != right.len() {
            return false;
        }
        left.iter()
            .zip(right.iter())
            .all(|(a, b)| self.objs_have_same_known_equality_rc_in_some_env(a, b))
    }

    pub fn try_verify_equal_by_same_shape_and_known_equality_args(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        let reason = "same shape and paired args share known equality class";
        match (left, right) {
            (Obj::FnObj(left_fn), Obj::FnObj(right_fn)) => {
                let left_head_obj = left_fn.head.as_ref().clone().into();
                let right_head_obj = right_fn.head.as_ref().clone().into();
                if !verify_equality_by_they_are_the_same(&left_head_obj, &right_head_obj) {
                    return Some((StmtUnknown::new()).into());
                }
                if left_fn.body.len() != right_fn.body.len() {
                    return Some((StmtUnknown::new()).into());
                }
                for (left_group, right_group) in left_fn.body.iter().zip(right_fn.body.iter()) {
                    if !self.boxed_obj_vecs_share_known_equality_class(left_group, right_group) {
                        return Some((StmtUnknown::new()).into());
                    }
                }
                Some(factual_equal_success_by_builtin_reason(
                    left, right, line_file, reason,
                ))
            }
            (Obj::Add(l), Obj::Add(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixAdd(l), Obj::MatrixAdd(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixSub(l), Obj::MatrixSub(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixMul(l), Obj::MatrixMul(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixScalarMul(l), Obj::MatrixScalarMul(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.scalar, &r.scalar),
                    (&l.matrix, &r.matrix),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixPow(l), Obj::MatrixPow(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.base, &r.base),
                    (&l.exponent, &r.exponent),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Sub(l), Obj::Sub(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Mul(l), Obj::Mul(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Div(l), Obj::Div(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Mod(l), Obj::Mod(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Pow(l), Obj::Pow(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.base, &r.base),
                    (&l.exponent, &r.exponent),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Log(l), Obj::Log(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.base, &r.base), (&l.arg, &r.arg)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Max(l), Obj::Max(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Min(l), Obj::Min(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Union(l), Obj::Union(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Intersect(l), Obj::Intersect(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::SetMinus(l), Obj::SetMinus(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::SetDiff(l), Obj::SetDiff(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Cup(l), Obj::Cup(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.left, &r.left) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Cap(l), Obj::Cap(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.left, &r.left) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::PowerSet(l), Obj::PowerSet(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Choose(l), Obj::Choose(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::CartDim(l), Obj::CartDim(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::TupleDim(l), Obj::TupleDim(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.arg, &r.arg) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Count(l), Obj::Count(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Range(l), Obj::Range(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.start, &r.start), (&l.end, &r.end)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::ClosedRange(l), Obj::ClosedRange(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.start, &r.start), (&l.end, &r.end)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::FiniteSeqSet(l), Obj::FiniteSeqSet(r)) => {
                if self.arg_pairs_share_known_equality_class(&[(&l.set, &r.set), (&l.n, &r.n)]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::SeqSet(l), Obj::SeqSet(r)) => {
                if self.arg_pairs_share_known_equality_class(&[(&l.set, &r.set)]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixSet(l), Obj::MatrixSet(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.set, &r.set),
                    (&l.row_len, &r.row_len),
                    (&l.col_len, &r.col_len),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Proj(l), Obj::Proj(r)) => {
                if self.arg_pairs_share_known_equality_class(&[(&l.set, &r.set), (&l.dim, &r.dim)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::ObjAtIndex(l), Obj::ObjAtIndex(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.obj, &r.obj), (&l.index, &r.index)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Tuple(l), Obj::Tuple(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.args, &r.args) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::ListSet(l), Obj::ListSet(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.list, &r.list) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Cart(l), Obj::Cart(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.args, &r.args) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            _ => None,
        }
    }

    pub fn verify_equality_by_they_are_the_same_and_calculation(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<(StmtResult, Obj, Obj), RuntimeError> {
        if verify_equality_by_they_are_the_same(left, right) {
            return Ok((
                factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "they are the same",
                ),
                left.clone(),
                right.clone(),
            ));
        }

        let left_resolved = self.resolve_obj(left);
        let right_resolved = self.resolve_obj(right);

        if left_resolved.two_objs_can_be_calculated_and_equal_by_calculation(&right_resolved) {
            return Ok((
                factual_equal_success_by_builtin_reason(left, right, line_file, "calculation"),
                left_resolved,
                right_resolved,
            ));
        }

        Ok((
            StmtResult::StmtUnknown(StmtUnknown::new()),
            left_resolved,
            right_resolved,
        ))
    }
}
