use crate::prelude::*;
use crate::verify::verify_builtin_rules::{
    compare_normalized_number_str_to_zero, NumberCompareResult,
};
use crate::verify::verify_number_in_standard_set::is_integer_after_simplification;
use std::collections::HashMap;
use std::rc::Rc;

/// Structural alignment for builtin patterns: two objects match iff their `Display` text matches.
#[inline]
pub fn objs_equal_by_display_string(a: &Obj, b: &Obj) -> bool {
    a.to_string() == b.to_string()
}

pub fn verify_equality_by_they_are_the_same(left: &Obj, right: &Obj) -> bool {
    objs_equal_by_display_string(left, right)
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

    // `sum(i, a, b, F) = sum(i, a', b', G)` when `i` matches on both sides: prove `a = a'`, `b = b'` with full
    // `verify_objs_are_equal`, then in a local env register `i` as sum index, assume `i in Z`, `a <= i <= b`,
    // and prove `F = G` with `verify_objs_are_equal`.
    fn try_verify_two_sums_equal_by_pointwise_body(
        &mut self,
        left: &SumObj,
        right: &SumObj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if left.param != right.param {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal(
                left.start.as_ref(),
                right.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal(
                left.end.as_ref(),
                right.end.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let param_name = left.param.clone();
        let start_obj = (*left.start).clone();
        let end_obj = (*left.end).clone();
        let bodies_equal = self.run_in_local_env(|rt| {
            rt.store_free_param_or_identifier_name(&param_name, ParamObjType::Sum)?;
            let param_obj = obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Sum);
            let param_in_z: AtomicFact = InFact::new(
                param_obj.clone(),
                StandardSet::Z.into(),
                default_line_file(),
            )
            .into();
            rt.store_atomic_fact_without_well_defined_verified_and_infer(param_in_z)?;
            let lower: AtomicFact =
                LessEqualFact::new(start_obj.clone(), param_obj.clone(), default_line_file()).into();
            rt.store_atomic_fact_without_well_defined_verified_and_infer(lower)?;
            let upper: AtomicFact = LessEqualFact::new(param_obj, end_obj, default_line_file()).into();
            rt.store_atomic_fact_without_well_defined_verified_and_infer(upper)?;
            let stmt = rt.verify_objs_are_equal(
                left.body.as_ref(),
                right.body.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            Ok::<bool, RuntimeError>(stmt.is_true())
        })?;
        if !bodies_equal {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            &left.clone().into(),
            &right.clone().into(),
            line_file,
            "equality: two sums same index and bounds; summands equal under index assumptions",
        )))
    }

    fn try_verify_two_sums_pointwise_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let (Obj::Sum(lsum), Obj::Sum(rsum)) = (left, right) {
            return self.try_verify_two_sums_equal_by_pointwise_body(
                lsum, rsum, line_file, verify_state,
            );
        }
        Ok(None)
    }

    // product(i,a,e+1,F) = product(i,a,e,F) * tail: extending the upper index multiplies by F with i ↦ outer end.
    // Example: product(i, start, last + 1, i) = product(i, start, last, i) * (last + 1) when tail matches inst body.
    // Same structural checks as sum peel but * and ParamObjType::Product.
    fn try_finish_product_peel_equality(
        &mut self,
        outer: &ProductObj,
        inner: &ProductObj,
        actual_tail: &Obj,
        _verify_state: &VerifyState,
    ) -> Result<Option<()>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        if outer.param != inner.param {
            return Ok(None);
        }
        if !objs_equal_by_display_string(outer.start.as_ref(), inner.start.as_ref()) {
            return Ok(None);
        }
        if !objs_equal_by_display_string(outer.body.as_ref(), inner.body.as_ref()) {
            return Ok(None);
        }
        let end_plus_one: Obj = Add::new((*inner.end).clone(), one.clone()).into();
        if !objs_equal_by_display_string(outer.end.as_ref(), &end_plus_one) {
            return Ok(None);
        }
        let mut m = HashMap::new();
        m.insert(outer.param.clone(), (*outer.end).clone());
        let Ok(expected_tail) = self.inst_obj(outer.body.as_ref(), &m, ParamObjType::Product) else {
            return Ok(None);
        };
        if !objs_equal_by_display_string(actual_tail, &expected_tail) {
            return Ok(None);
        }
        Ok(Some(()))
    }

    fn try_verify_product_peel_last_factor_equality(
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
                        if self.try_finish_product_peel_equality(
                            lprod,
                            rprod,
                            tail_side,
                            verify_state,
                        )? == Some(())
                        {
                            return Ok(Some(factual_equal_success_by_builtin_reason(
                                left,
                                right,
                                line_file,
                                "equality: product upper +1 = inner product * factor at new index",
                            )));
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
                        if self.try_finish_product_peel_equality(
                            rprod,
                            lprod,
                            tail_side,
                            verify_state,
                        )? == Some(())
                        {
                            return Ok(Some(factual_equal_success_by_builtin_reason(
                                left,
                                right,
                                line_file,
                                "equality: product upper +1 = inner product * factor at new index",
                            )));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    // sum(i,a,e+1,F) = sum(i,a,e,F) + tail with i bound to outer end (same i,a,F; one binary + on the other side).
    // Aligned parts use objs_equal_by_display_string (including outer end vs inner end + 1 and tail vs inst_obj).
    fn try_finish_sum_peel_equality(
        &mut self,
        outer: &SumObj,
        inner: &SumObj,
        actual_tail: &Obj,
        _verify_state: &VerifyState,
    ) -> Result<Option<()>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        if outer.param != inner.param {
            return Ok(None);
        }
        if !objs_equal_by_display_string(outer.start.as_ref(), inner.start.as_ref()) {
            return Ok(None);
        }
        if !objs_equal_by_display_string(outer.body.as_ref(), inner.body.as_ref()) {
            return Ok(None);
        }
        let end_plus_one: Obj = Add::new((*inner.end).clone(), one.clone()).into();
        if !objs_equal_by_display_string(outer.end.as_ref(), &end_plus_one) {
            return Ok(None);
        }
        let mut m = HashMap::new();
        m.insert(outer.param.clone(), (*outer.end).clone());
        let Ok(expected_tail) = self.inst_obj(outer.body.as_ref(), &m, ParamObjType::Sum) else {
            return Ok(None);
        };
        if !objs_equal_by_display_string(actual_tail, &expected_tail) {
            return Ok(None);
        }
        Ok(Some(()))
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
                        if self.try_finish_sum_peel_equality(
                            lsum,
                            rsum,
                            tail_side,
                            verify_state,
                        )? == Some(())
                        {
                            return Ok(Some(factual_equal_success_by_builtin_reason(
                                left,
                                right,
                                line_file,
                                "equality: sum upper +1 = inner sum + term at new index",
                            )));
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
                        if self.try_finish_sum_peel_equality(
                            rsum,
                            lsum,
                            tail_side,
                            verify_state,
                        )? == Some(())
                        {
                            return Ok(Some(factual_equal_success_by_builtin_reason(
                                left,
                                right,
                                line_file,
                                "equality: sum upper +1 = inner sum + term at new index",
                            )));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    // sum(i,a,b,F+G) = sum(i,a,b,F) + sum(i,a,b,G); other side is one binary + with two sums (order either way).
    // Bounds and F,G vs inner bodies: objs_equal_by_display_string.
    fn try_match_sum_additivity_one_direction(
        &mut self,
        outer: &SumObj,
        other: &Obj,
        _line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Add(body_add) = outer.body.as_ref() else {
            return Ok(false);
        };
        let Obj::Add(outer_add) = other else {
            return Ok(false);
        };
        for (x_side, y_side) in [
            (outer_add.left.as_ref(), outer_add.right.as_ref()),
            (outer_add.right.as_ref(), outer_add.left.as_ref()),
        ] {
            if let (Obj::Sum(sx), Obj::Sum(sy)) = (x_side, y_side) {
                if outer.param != sx.param || outer.param != sy.param {
                    continue;
                }
                if !objs_equal_by_display_string(outer.start.as_ref(), sx.start.as_ref()) {
                    continue;
                }
                if !objs_equal_by_display_string(outer.start.as_ref(), sy.start.as_ref()) {
                    continue;
                }
                if !objs_equal_by_display_string(outer.end.as_ref(), sx.end.as_ref()) {
                    continue;
                }
                if !objs_equal_by_display_string(outer.end.as_ref(), sy.end.as_ref()) {
                    continue;
                }
                let fl = body_add.left.as_ref();
                let fr = body_add.right.as_ref();
                let match_fg = objs_equal_by_display_string(fl, sx.body.as_ref())
                    && objs_equal_by_display_string(fr, sy.body.as_ref());
                let match_gf = objs_equal_by_display_string(fl, sy.body.as_ref())
                    && objs_equal_by_display_string(fr, sx.body.as_ref());
                if match_fg || match_gf {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn try_verify_sum_additivity_same_bounds_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Sum(lsum) = left {
            if self.try_match_sum_additivity_one_direction(
                lsum,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum(summand + summand) = sum + sum same bounds",
                )));
            }
        }
        if let Obj::Sum(rsum) = right {
            if self.try_match_sum_additivity_one_direction(
                rsum,
                left,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum(summand + summand) = sum + sum same bounds",
                )));
            }
        }
        Ok(None)
    }

    // product(i,a,b,F*G) = product(i,a,b,F) * product(i,a,b,G); one * on the other side with two inner products (order either way).
    // Index name matches on all three; start/end vs each inner product use verify_objs_are_equal; factors vs inner bodies use display text.
    // Example: product(i, s, t, i * i) = product(i, s, t, i) * product(i, s, t, i).
    fn try_match_product_multiplicativity_one_direction(
        &mut self,
        outer: &ProductObj,
        other: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Mul(body_mul) = outer.body.as_ref() else {
            return Ok(false);
        };
        let Obj::Mul(outer_mul) = other else {
            return Ok(false);
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
                let match_fg = objs_equal_by_display_string(fl, px.body.as_ref())
                    && objs_equal_by_display_string(fr, py.body.as_ref());
                let match_gf = objs_equal_by_display_string(fl, py.body.as_ref())
                    && objs_equal_by_display_string(fr, px.body.as_ref());
                if match_fg || match_gf {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn try_verify_product_multiplicativity_same_bounds_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Product(lprod) = left {
            if self.try_match_product_multiplicativity_one_direction(
                lprod,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: product(factor * factor) = product * product same bounds",
                )));
            }
        }
        if let Obj::Product(rprod) = right {
            if self.try_match_product_multiplicativity_one_direction(
                rprod,
                left,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: product(factor * factor) = product * product same bounds",
                )));
            }
        }
        Ok(None)
    }

    // sum(i,a,a,F) = inst(F, { i ↦ a }) when start and end match by objs_equal_by_display_string; RHS same for inst body.
    fn try_match_sum_single_index_interval_one_direction(
        &mut self,
        s: &SumObj,
        other: &Obj,
        _line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        if !objs_equal_by_display_string(s.start.as_ref(), s.end.as_ref()) {
            return Ok(false);
        }
        let mut m = HashMap::new();
        m.insert(s.param.clone(), (*s.start).clone());
        let Ok(inst_body) = self.inst_obj(s.body.as_ref(), &m, ParamObjType::Sum) else {
            return Ok(false);
        };
        if !objs_equal_by_display_string(&inst_body, other) {
            return Ok(false);
        }
        Ok(true)
    }

    fn try_verify_sum_single_index_interval_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Sum(lsum) = left {
            if self.try_match_sum_single_index_interval_one_direction(
                lsum,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum with start = end is single instantiated summand",
                )));
            }
        }
        if let Obj::Sum(rsum) = right {
            if self.try_match_sum_single_index_interval_one_direction(
                rsum,
                left,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum with start = end is single instantiated summand",
                )));
            }
        }
        Ok(None)
    }

    // product(i,a,a,F) = inst(F, { i ↦ a }) when start and end match by objs_equal_by_display_string; other side matches inst body.
    // Example: product(i, start, start, i) = start.
    fn try_match_product_single_index_interval_one_direction(
        &mut self,
        p: &ProductObj,
        other: &Obj,
        _line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        if !objs_equal_by_display_string(p.start.as_ref(), p.end.as_ref()) {
            return Ok(false);
        }
        let mut m = HashMap::new();
        m.insert(p.param.clone(), (*p.start).clone());
        let Ok(inst_body) = self.inst_obj(p.body.as_ref(), &m, ParamObjType::Product) else {
            return Ok(false);
        };
        if !objs_equal_by_display_string(&inst_body, other) {
            return Ok(false);
        }
        Ok(true)
    }

    fn try_verify_product_single_index_interval_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Product(lprod) = left {
            if self.try_match_product_single_index_interval_one_direction(
                lprod,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: product with start = end is single instantiated factor",
                )));
            }
        }
        if let Obj::Product(rprod) = right {
            if self.try_match_product_single_index_interval_one_direction(
                rprod,
                left,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: product with start = end is single instantiated factor",
                )));
            }
        }
        Ok(None)
    }

    // sum(i,a,b,F) = sum(i,a,k,F) + sum(i,k+1,b,F): same i,a,b,F; first segment ends at k, second starts at k+1.
    // Matching uses objs_equal_by_display_string (including k+1 vs second start).
    fn try_verify_sum_split_adjacent_segments_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _verify_state: &VerifyState,
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
                        if !objs_equal_by_display_string(lsum.start.as_ref(), s1.start.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(lsum.end.as_ref(), s2.end.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(lsum.body.as_ref(), s1.body.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(lsum.body.as_ref(), s2.body.as_ref()) {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*s1.end).clone(), one.clone()).into();
                        if !objs_equal_by_display_string(
                            &first_end_plus_one,
                            s2.start.as_ref(),
                        ) {
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
                        if !objs_equal_by_display_string(rsum.start.as_ref(), s1.start.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(rsum.end.as_ref(), s2.end.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(rsum.body.as_ref(), s1.body.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(rsum.body.as_ref(), s2.body.as_ref()) {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*s1.end).clone(), one.clone()).into();
                        if !objs_equal_by_display_string(
                            &first_end_plus_one,
                            s2.start.as_ref(),
                        ) {
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

    // product(i,a,k,F) * product(i,k+1,b,F) = product(i,a,b,F): same i and body on all three; a,b line up with
    // outer start/end; first segment end + 1 matches second start (objs_equal_by_display_string). Dual: one product = two factors.
    // Example: product(i, start, middle, i) * product(i, middle + 1, last, i) = product(i, start, last, i).
    fn try_verify_product_merge_adjacent_segments_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        if let Obj::Mul(mul) = left {
            if let Obj::Product(p_full) = right {
                for (p1_side, p2_side) in [
                    (mul.left.as_ref(), mul.right.as_ref()),
                    (mul.right.as_ref(), mul.left.as_ref()),
                ] {
                    if let (Obj::Product(p1), Obj::Product(p2)) = (p1_side, p2_side) {
                        if p_full.param != p1.param || p_full.param != p2.param {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.start.as_ref(), p1.start.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.end.as_ref(), p2.end.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.body.as_ref(), p1.body.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.body.as_ref(), p2.body.as_ref()) {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*p1.end).clone(), one.clone()).into();
                        if !objs_equal_by_display_string(
                            &first_end_plus_one,
                            p2.start.as_ref(),
                        ) {
                            continue;
                        }
                        return Ok(Some(factual_equal_success_by_builtin_reason(
                            left,
                            right,
                            line_file,
                            "equality: product merges adjacent segments (end+1 = next start)",
                        )));
                    }
                }
            }
        }
        if let Obj::Mul(mul) = right {
            if let Obj::Product(p_full) = left {
                for (p1_side, p2_side) in [
                    (mul.left.as_ref(), mul.right.as_ref()),
                    (mul.right.as_ref(), mul.left.as_ref()),
                ] {
                    if let (Obj::Product(p1), Obj::Product(p2)) = (p1_side, p2_side) {
                        if p_full.param != p1.param || p_full.param != p2.param {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.start.as_ref(), p1.start.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.end.as_ref(), p2.end.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.body.as_ref(), p1.body.as_ref()) {
                            continue;
                        }
                        if !objs_equal_by_display_string(p_full.body.as_ref(), p2.body.as_ref()) {
                            continue;
                        }
                        let first_end_plus_one: Obj =
                            Add::new((*p1.end).clone(), one.clone()).into();
                        if !objs_equal_by_display_string(
                            &first_end_plus_one,
                            p2.start.as_ref(),
                        ) {
                            continue;
                        }
                        return Ok(Some(factual_equal_success_by_builtin_reason(
                            left,
                            right,
                            line_file,
                            "equality: product merges adjacent segments (end+1 = next start)",
                        )));
                    }
                }
            }
        }
        Ok(None)
    }

    // sum(i,a,b,k*c) = k * sum(i,a,b,c): same param string; start, end, summand c, and factor k match by
    // obj Display text (objs_equal_by_display_string). Requires k well-defined and every sum/product index
    // atom in k bound by an enclosing sum/product (k must not use the outer i).
    // Example: sum(n,1,3,2*n) = 2 * sum(n,1,3,n).
    fn try_match_sum_scalar_factor_out_one_direction(
        &mut self,
        outer: &SumObj,
        other: &Obj,
        _line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let Obj::Mul(body_mul) = outer.body.as_ref() else {
            return Ok(false);
        };
        let Obj::Mul(rhs_mul) = other else {
            return Ok(false);
        };
        for (lk, lc) in [
            (body_mul.left.as_ref(), body_mul.right.as_ref()),
            (body_mul.right.as_ref(), body_mul.left.as_ref()),
        ] {
            for (rk_factor, rk_sum_side) in [
                (rhs_mul.left.as_ref(), rhs_mul.right.as_ref()),
                (rhs_mul.right.as_ref(), rhs_mul.left.as_ref()),
            ] {
                let Obj::Sum(inner) = rk_sum_side else {
                    continue;
                };
                if outer.param != inner.param {
                    continue;
                }
                if !objs_equal_by_display_string(outer.start.as_ref(), inner.start.as_ref()) {
                    continue;
                }
                if !objs_equal_by_display_string(outer.end.as_ref(), inner.end.as_ref()) {
                    continue;
                }
                if !objs_equal_by_display_string(lc, inner.body.as_ref()) {
                    continue;
                }
                if !objs_equal_by_display_string(lk, rk_factor) {
                    continue;
                }
                if self
                    .verify_obj_well_defined_and_store_cache(lk, verify_state)
                    .is_err()
                {
                    continue;
                }
                let mut bound = Vec::new();
                if !obj_lexically_bound_sum_product_index_atoms(lk, &mut bound) {
                    continue;
                }
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn try_verify_sum_scalar_factor_out_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::Sum(lsum) = left {
            if self.try_match_sum_scalar_factor_out_one_direction(
                lsum,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum(k * summand) = k * sum(summand) with k well-defined and independent of sum index",
                )));
            }
        }
        if let Obj::Sum(rsum) = right {
            if self.try_match_sum_scalar_factor_out_one_direction(
                rsum,
                left,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum(k * summand) = k * sum(summand) with k well-defined and independent of sum index",
                )));
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

        if let Some(done) = self.try_verify_two_sums_pointwise_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
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

        if let Some(done) = self.try_verify_product_peel_last_factor_equality(
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

        if let Some(done) = self.try_verify_product_multiplicativity_same_bounds_equality(
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

        if let Some(done) = self.try_verify_product_single_index_interval_equality(
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

        if let Some(done) = self.try_verify_product_merge_adjacent_segments_equality(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        if let Some(done) = self.try_verify_sum_scalar_factor_out_equality(
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

/// Every `AtomObj::Sum` / `AtomObj::Product` spine in `obj` must be bound by some enclosing
/// `Obj::Sum` / `Obj::Product` with the same index name (nested binders may shadow).
fn obj_lexically_bound_sum_product_index_atoms(obj: &Obj, bound: &mut Vec<String>) -> bool {
    match obj {
        Obj::Sum(s) => {
            bound.push(s.param.clone());
            let ok = obj_lexically_bound_sum_product_index_atoms(s.start.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(s.end.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(s.body.as_ref(), bound);
            bound.pop();
            ok
        }
        Obj::Product(p) => {
            bound.push(p.param.clone());
            let ok = obj_lexically_bound_sum_product_index_atoms(p.start.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(p.end.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(p.body.as_ref(), bound);
            bound.pop();
            ok
        }
        Obj::Atom(AtomObj::Sum(p)) => bound.iter().any(|n| n == &p.name),
        Obj::Atom(AtomObj::Product(p)) => bound.iter().any(|n| n == &p.name),
        Obj::Atom(_) => true,
        Obj::FnObj(f) => {
            let head: Obj = f.head.as_ref().clone().into();
            if !obj_lexically_bound_sum_product_index_atoms(&head, bound) {
                return false;
            }
            f.body.iter().all(|g| {
                g.iter()
                    .all(|o| obj_lexically_bound_sum_product_index_atoms(o.as_ref(), bound))
            })
        }
        Obj::Number(_) | Obj::StandardSet(_) => true,
        Obj::Add(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Sub(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Mul(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Div(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Mod(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Pow(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.base.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.exponent.as_ref(), bound)
        }
        Obj::MatrixAdd(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::MatrixSub(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::MatrixMul(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::MatrixScalarMul(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.scalar.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.matrix.as_ref(), bound)
        }
        Obj::MatrixPow(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.base.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.exponent.as_ref(), bound)
        }
        Obj::Abs(x) => obj_lexically_bound_sum_product_index_atoms(x.arg.as_ref(), bound),
        Obj::Log(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.base.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.arg.as_ref(), bound)
        }
        Obj::Max(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Min(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Union(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Intersect(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::SetMinus(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::SetDiff(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.right.as_ref(), bound)
        }
        Obj::Cup(x) => obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound),
        Obj::Cap(x) => obj_lexically_bound_sum_product_index_atoms(x.left.as_ref(), bound),
        Obj::PowerSet(x) => obj_lexically_bound_sum_product_index_atoms(x.set.as_ref(), bound),
        Obj::ListSet(ls) => ls
            .list
            .iter()
            .all(|o| obj_lexically_bound_sum_product_index_atoms(o.as_ref(), bound)),
        Obj::SetBuilder(sb) => {
            if !obj_lexically_bound_sum_product_index_atoms(sb.param_set.as_ref(), bound) {
                return false;
            }
            sb.facts
                .iter()
                .all(|f| or_and_chain_lexically_bound_sum_product_index_atoms(f, bound))
        }
        Obj::FnSet(fs) => {
            if !fs.params_def_with_set.iter().all(|ps| {
                obj_lexically_bound_sum_product_index_atoms(&ps.set, bound)
            }) {
                return false;
            }
            if !fs
                .dom_facts
                .iter()
                .all(|df| or_and_chain_lexically_bound_sum_product_index_atoms(df, bound))
            {
                return false;
            }
            obj_lexically_bound_sum_product_index_atoms(fs.ret_set.as_ref(), bound)
        }
        Obj::Cart(c) => c
            .args
            .iter()
            .all(|a| obj_lexically_bound_sum_product_index_atoms(a.as_ref(), bound)),
        Obj::CartDim(x) => obj_lexically_bound_sum_product_index_atoms(x.set.as_ref(), bound),
        Obj::Proj(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.set.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.dim.as_ref(), bound)
        }
        Obj::TupleDim(x) => obj_lexically_bound_sum_product_index_atoms(x.arg.as_ref(), bound),
        Obj::Tuple(t) => t
            .args
            .iter()
            .all(|a| obj_lexically_bound_sum_product_index_atoms(a.as_ref(), bound)),
        Obj::Count(x) => obj_lexically_bound_sum_product_index_atoms(x.set.as_ref(), bound),
        Obj::Range(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.start.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.end.as_ref(), bound)
        }
        Obj::ClosedRange(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.start.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.end.as_ref(), bound)
        }
        Obj::FiniteSeqSet(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.set.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.n.as_ref(), bound)
        }
        Obj::SeqSet(x) => obj_lexically_bound_sum_product_index_atoms(x.set.as_ref(), bound),
        Obj::FiniteSeqListObj(v) => v.objs.iter().all(|o| {
            obj_lexically_bound_sum_product_index_atoms(o.as_ref(), bound)
        }),
        Obj::MatrixSet(ms) => {
            obj_lexically_bound_sum_product_index_atoms(ms.set.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(ms.row_len.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(ms.col_len.as_ref(), bound)
        }
        Obj::MatrixListObj(v) => v.rows.iter().all(|row| {
            row.iter()
                .all(|o| obj_lexically_bound_sum_product_index_atoms(o.as_ref(), bound))
        }),
        Obj::Choose(x) => obj_lexically_bound_sum_product_index_atoms(x.set.as_ref(), bound),
        Obj::ObjAtIndex(x) => {
            obj_lexically_bound_sum_product_index_atoms(x.obj.as_ref(), bound)
                && obj_lexically_bound_sum_product_index_atoms(x.index.as_ref(), bound)
        }
        Obj::FamilyObj(f) => f
            .params
            .iter()
            .all(|o| obj_lexically_bound_sum_product_index_atoms(o, bound)),
    }
}

fn or_and_chain_lexically_bound_sum_product_index_atoms(
    parent_fact: &OrAndChainAtomicFact,
    bound: &mut Vec<String>,
) -> bool {
    match parent_fact {
        OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
            atomic_fact_lexically_bound_sum_product_index_atoms(atomic_fact, bound)
        }
        OrAndChainAtomicFact::AndFact(and_fact) => and_fact
            .facts
            .iter()
            .all(|f| atomic_fact_lexically_bound_sum_product_index_atoms(f, bound)),
        OrAndChainAtomicFact::ChainFact(chain_fact) => chain_fact
            .objs
            .iter()
            .all(|o| obj_lexically_bound_sum_product_index_atoms(o, bound)),
        OrAndChainAtomicFact::OrFact(or_fact) => or_fact
            .facts
            .iter()
            .all(|b| and_chain_lexically_bound_sum_product_index_atoms(b, bound)),
    }
}

fn and_chain_lexically_bound_sum_product_index_atoms(
    parent_fact: &AndChainAtomicFact,
    bound: &mut Vec<String>,
) -> bool {
    match parent_fact {
        AndChainAtomicFact::AtomicFact(atomic_fact) => {
            atomic_fact_lexically_bound_sum_product_index_atoms(atomic_fact, bound)
        }
        AndChainAtomicFact::AndFact(and_fact) => and_fact
            .facts
            .iter()
            .all(|f| atomic_fact_lexically_bound_sum_product_index_atoms(f, bound)),
        AndChainAtomicFact::ChainFact(chain_fact) => chain_fact
            .objs
            .iter()
            .all(|o| obj_lexically_bound_sum_product_index_atoms(o, bound)),
    }
}

fn atomic_fact_lexically_bound_sum_product_index_atoms(
    fact: &AtomicFact,
    bound: &mut Vec<String>,
) -> bool {
    match fact {
        AtomicFact::NormalAtomicFact(fact) => fact
            .body
            .iter()
            .all(|o| obj_lexically_bound_sum_product_index_atoms(o, bound)),
        AtomicFact::NotNormalAtomicFact(fact) => fact
            .body
            .iter()
            .all(|o| obj_lexically_bound_sum_product_index_atoms(o, bound)),
        AtomicFact::EqualFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::LessFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::GreaterFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::LessEqualFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::GreaterEqualFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::NotEqualFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::NotLessFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::NotGreaterFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::NotLessEqualFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::NotGreaterEqualFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::IsSetFact(fact) => obj_lexically_bound_sum_product_index_atoms(&fact.set, bound),
        AtomicFact::NotIsSetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::IsNonemptySetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::NotIsNonemptySetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::IsFiniteSetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::NotIsFiniteSetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::InFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.element, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::NotInFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.element, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::IsCartFact(fact) => obj_lexically_bound_sum_product_index_atoms(&fact.set, bound),
        AtomicFact::NotIsCartFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::IsTupleFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::NotIsTupleFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.set, bound)
        }
        AtomicFact::SubsetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::SupersetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::NotSubsetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::NotSupersetFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.left, bound)
                && obj_lexically_bound_sum_product_index_atoms(&fact.right, bound)
        }
        AtomicFact::RestrictFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.obj, bound)
                && obj_lexically_bound_sum_product_index_atoms(
                    &fact.obj_can_restrict_to_fn_set,
                    bound,
                )
        }
        AtomicFact::NotRestrictFact(fact) => {
            obj_lexically_bound_sum_product_index_atoms(&fact.obj, bound)
                && obj_lexically_bound_sum_product_index_atoms(
                    &fact.obj_cannot_restrict_to_fn_set,
                    bound,
                )
        }
    }
}
