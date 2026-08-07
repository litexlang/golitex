use super::*;

fn direct_additive_range_shift(base: &Obj, translated: &Obj) -> Option<Obj> {
    let Obj::Add(add) = translated else {
        return None;
    };
    if add.left.to_string() == base.to_string() {
        return Some(add.right.as_ref().clone());
    }
    if add.right.to_string() == base.to_string() {
        return Some(add.left.as_ref().clone());
    }
    None
}

impl Runtime {
    /// A finite integer-range sum of the literal zero function is zero.
    pub(crate) fn try_verify_literal_zero_range_sum_is_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let sum = if Self::obj_is_builtin_literal_zero(left) {
            match right {
                Obj::Sum(sum) => sum,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_zero(right) {
            match left {
                Obj::Sum(sum) => sum,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        let probe: Obj = Number::new("1".to_string()).into();
        let Some(value) = self.instantiate_unary_anonymous_summand_at(sum.func.as_ref(), &probe)?
        else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_zero(&value) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: a finite range sum of the literal zero function is zero",
        )))
    }

    /// `sum(s,e,f) = sum(s,e,g)` when `f(x) = g(x)` is known for every integer
    /// `x` in the shared closed range. Example: after proving
    /// `forall x Z: s <= x, x <= e => f(x) = g(x)`, the two sums are equal.
    pub(crate) fn try_verify_sum_pointwise_congruence(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Sum(left_sum), Obj::Sum(right_sum)) = (left, right) else {
            return Ok(None);
        };

        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_sum.start.as_ref(),
                right_sum.start.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            .is_true()
            || !self
                .verify_objs_are_equal_in_equality_builtin(
                    left_sum.end.as_ref(),
                    right_sum.end.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
        {
            return Ok(None);
        }

        let unary_param_set = |func: &Obj| -> Option<Obj> {
            let af = match func {
                Obj::AnonymousFn(af) => af,
                Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(af) => af.as_ref(),
                    _ => return None,
                },
                _ => return None,
            };
            if af.body.params_def_with_set.number_of_params() != 1
                || af.body.params_def_with_set.len() != 1
            {
                return None;
            }
            Some(af.body.params_def_with_set.as_slice()[0].set_obj().clone())
        };
        let index_param_set = match (
            unary_param_set(left_sum.func.as_ref()),
            unary_param_set(right_sum.func.as_ref()),
        ) {
            (Some(left_set), Some(right_set))
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        &left_set,
                        &right_set,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true() =>
            {
                left_set
            }
            _ => StandardSet::Z.into(),
        };

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name, ParamObjType::Forall)?;
        let Some(left_value) =
            self.instantiate_unary_anonymous_summand_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_value) =
            self.instantiate_unary_anonymous_summand_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let pointwise_fact: AtomicFact =
            EqualFact::new(left_value, right_value, line_file.clone()).into();
        let lower_bound: Fact =
            LessEqualFact::new((*left_sum.start).clone(), x_obj.clone(), line_file.clone()).into();
        let upper_bound: Fact =
            LessEqualFact::new(x_obj, (*left_sum.end).clone(), line_file.clone()).into();

        let pointwise_result = self.run_in_local_env(|rt| {
            let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_binding],
                ParamType::Obj(index_param_set),
            )]);
            rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
            rt.store_fact_without_forall_coverage_check_and_infer(lower_bound)?;
            rt.store_fact_without_forall_coverage_check_and_infer(upper_bound)?;

            let known_forall_result = rt.verify_atomic_fact_with_known_forall(
                &pointwise_fact,
                &UseContextVerifyState::new(0, true),
            )?;
            if known_forall_result.is_true() {
                return Ok(known_forall_result);
            }
            rt.verify_builtin_rule_premise(&pointwise_fact, builtin_state)
        })?;
        if !pointwise_result.is_true() {
            return Ok(None);
        }

        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: finite sums are congruent from pointwise equality on the shared integer range",
        )))
    }

    /// `sum(s,e,f) = sum(s,e,g) + sum(s,e,h)` when for all integer `x` with `s <= x <= e`,
    /// `f(x) = g(x) + h(x)` (summands are unary anonymous `fn` bodies, instantiated at `x`).
    pub(crate) fn try_verify_sum_additivity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (sum_m, sum_a, sum_b) = match (left, right) {
            (Obj::Sum(m), Obj::Add(a)) => match (a.left.as_ref(), a.right.as_ref()) {
                (Obj::Sum(a1), Obj::Sum(a2)) => (m, a1, a2),
                _ => return Ok(None),
            },
            (Obj::Add(a), Obj::Sum(m)) => match (a.left.as_ref(), a.right.as_ref()) {
                (Obj::Sum(a1), Obj::Sum(a2)) => (m, a1, a2),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };

        let mut require_eq = |a: &Obj, b: &Obj| -> Result<bool, RuntimeError> {
            Ok(self
                .verify_objs_are_equal_in_equality_builtin(a, b, line_file.clone(), builtin_state)?
                .is_true())
        };
        if !require_eq(sum_m.start.as_ref(), sum_a.start.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.start.as_ref(), sum_b.start.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.end.as_ref(), sum_a.end.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.end.as_ref(), sum_b.end.as_ref())? {
            return Ok(None);
        }

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name, ParamObjType::Forall)?;

        let Some(l_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_m.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(a_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_a.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(b_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_b.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let then_fact: AtomicFact =
            EqualFact::new(l_inst, Add::new(a_inst, b_inst).into(), line_file.clone()).into();

        let dom_lo: Fact =
            LessEqualFact::new((*sum_m.start).clone(), x_obj.clone(), line_file.clone()).into();
        let dom_hi: Fact =
            LessEqualFact::new(x_obj.clone(), (*sum_m.end).clone(), line_file.clone()).into();

        let r = self.verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
            x_binding,
            vec![dom_lo, dom_hi],
            &then_fact,
            builtin_state,
        )?;
        if r.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: sum additivity from pointwise equality on the integer index range",
            )));
        }
        Ok(None)
    }

    /// Finite sums distribute over pointwise subtraction on the same integer range.
    /// Example: `sum(m,n,fn(i Z) R {f(i)-g(i)}) = sum(m,n,f) - sum(m,n,g)`.
    pub(crate) fn try_verify_sum_subtraction(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (difference_sum, minuend_sum, subtrahend_sum) = match (left, right) {
            (Obj::Sum(sum), Obj::Sub(difference)) => {
                let (Obj::Sum(minuend), Obj::Sum(subtrahend)) =
                    (difference.left.as_ref(), difference.right.as_ref())
                else {
                    return Ok(None);
                };
                (sum, minuend, subtrahend)
            }
            (Obj::Sub(difference), Obj::Sum(sum)) => {
                let (Obj::Sum(minuend), Obj::Sum(subtrahend)) =
                    (difference.left.as_ref(), difference.right.as_ref())
                else {
                    return Ok(None);
                };
                (sum, minuend, subtrahend)
            }
            _ => return Ok(None),
        };

        for other_sum in [minuend_sum, subtrahend_sum] {
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    difference_sum.start.as_ref(),
                    other_sum.start.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
                || !self
                    .verify_objs_are_equal_in_equality_builtin(
                        difference_sum.end.as_ref(),
                        other_sum.end.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
            {
                return Ok(None);
            }
        }
        if !self.sum_functions_share_standard_additive_carrier([
            difference_sum.func.as_ref(),
            minuend_sum.func.as_ref(),
            subtrahend_sum.func.as_ref(),
        ]) {
            return Ok(None);
        }

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name, ParamObjType::Forall)?;
        let Some(difference_at_x) =
            self.instantiate_unary_anonymous_summand_at(difference_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(minuend_at_x) =
            self.instantiate_unary_anonymous_summand_at(minuend_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(subtrahend_at_x) =
            self.instantiate_unary_anonymous_summand_at(subtrahend_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let dom_lo: Fact = LessEqualFact::new(
            (*difference_sum.start).clone(),
            x_obj.clone(),
            line_file.clone(),
        )
        .into();
        let dom_hi: Fact =
            LessEqualFact::new(x_obj, (*difference_sum.end).clone(), line_file.clone()).into();
        let dom_facts = vec![dom_lo, dom_hi];

        let expected: Obj = Sub::new(minuend_at_x, subtrahend_at_x).into();
        let pointwise_fact: AtomicFact =
            EqualFact::new(difference_at_x, expected, line_file.clone()).into();
        let pointwise_result = self
            .verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
                x_binding,
                dom_facts,
                &pointwise_fact,
                builtin_state,
            )?;
        if !pointwise_result.is_true() {
            return Ok(None);
        }

        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: finite sum subtraction over a common additive carrier",
        )))
    }

    pub(crate) fn instantiate_unary_anonymous_summand_at(
        &mut self,
        func: &Obj,
        x: &Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        let af: &AnonymousFn = match func {
            Obj::AnonymousFn(af) => af,
            Obj::FnObj(fo) => {
                if !fo.body.is_empty() {
                    return Ok(None);
                }
                match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let param_defs = &af.body.params_def_with_set;
        let args = vec![x.clone()];
        let param_to_arg_map =
            ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(param_defs, &args);
        Ok(Some(self.inst_obj(
            af.equal_to.as_ref(),
            &param_to_arg_map,
            ParamObjType::FnSet,
        )?))
    }

    pub(crate) fn verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
        &mut self,
        param_binding: SymbolBinding,
        dom_facts: Vec<Fact>,
        then_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![param_binding],
                ParamType::Obj(StandardSet::Z.into()),
            )]);
            rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
            for dom_fact in dom_facts {
                rt.store_fact_without_forall_coverage_check_and_infer(dom_fact)?;
            }
            let known_forall_result = rt.verify_atomic_fact_with_known_forall(
                then_fact,
                &UseContextVerifyState::new(0, true),
            )?;
            if known_forall_result.is_true() {
                return Ok(known_forall_result);
            }
            rt.verify_builtin_rule_premise(then_fact, builtin_state)
        })
    }

    /// `sum(a..b) + sum((b+1)..c) = sum(a..c)` with the same unary anonymous summand on each side.
    pub(crate) fn try_verify_sum_merge_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (add, s3) = match (left, right) {
            (Obj::Add(a), Obj::Sum(s)) => (a, s),
            (Obj::Sum(s), Obj::Add(a)) => (a, s),
            _ => return Ok(None),
        };
        let (s1, s2) = match (add.left.as_ref(), add.right.as_ref()) {
            (Obj::Sum(x), Obj::Sum(y)) => (x, y),
            _ => return Ok(None),
        };
        for (a, b) in [(s1, s2), (s2, s1)] {
            if let Some(done) = self.try_verify_sum_merge_ordered_pair(
                a,
                b,
                s3,
                left,
                right,
                line_file.clone(),
                builtin_state,
            )? {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    pub(super) fn try_verify_sum_merge_ordered_pair(
        &mut self,
        s1: &Sum,
        s2: &Sum,
        s3: &Sum,
        stmt_left: &Obj,
        stmt_right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        let gap = Add::new((*s1.end).clone(), one).into();
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &gap,
                s2.start.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.start.as_ref(),
                s3.start.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s2.end.as_ref(),
                s3.end.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.func.as_ref(),
                s2.func.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.func.as_ref(),
                s3.func.as_ref(),
                line_file.clone(),
                builtin_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            stmt_left,
            stmt_right,
            line_file,
            "equality: merge adjacent sum ranges with the same summand",
        )))
    }

    // A finite sum over one index is the summand at that index.
    // Example: `sum(1, 1, fn(x N+) N+ {x}) = 1`.
    pub(crate) fn try_verify_sum_single_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (sum_obj, other) in [(left, right), (right, left)] {
            let Obj::Sum(sum) = sum_obj else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    sum.start.as_ref(),
                    sum.end.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            let Some(expected) =
                self.instantiate_unary_anonymous_summand_at(sum.func.as_ref(), sum.start.as_ref())?
            else {
                continue;
            };
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    &expected,
                    other,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: single-term sum equals the summand",
                )));
            }
        }
        Ok(None)
    }

    // A finite product over one index is the factor at that index.
    // Example: `product(1, 1, fn(x N+) N+ {x}) = 1`.
    pub(crate) fn try_verify_product_single_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (product_obj, other) in [(left, right), (right, left)] {
            let Obj::Product(product) = product_obj else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    product.start.as_ref(),
                    product.end.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            let Some(expected) = self.instantiate_unary_anonymous_summand_at(
                product.func.as_ref(),
                product.start.as_ref(),
            )?
            else {
                continue;
            };
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    &expected,
                    other,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: single-term product equals the factor",
                )));
            }
        }
        Ok(None)
    }

    // sum(s,e,f) = sum(s,e-1,f) + f(e): same unary summand, shared start, e = (e-1)+1 on the shorter range.
    pub(crate) fn try_verify_sum_split_last_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        for (full_obj, add_obj) in [(left, right), (right, left)] {
            let Obj::Sum(s_full) = full_obj else {
                continue;
            };
            let Obj::Add(a) = add_obj else {
                continue;
            };
            for (sum_part, tail) in [
                (a.left.as_ref(), a.right.as_ref()),
                (a.right.as_ref(), a.left.as_ref()),
            ] {
                let Obj::Sum(s_pre) = sum_part else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.start.as_ref(),
                        s_pre.start.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let end_pre_plus_one: Obj = Add::new((*s_pre.end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.func.as_ref(),
                        s_pre.func.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let Some(expected_tail) = self.instantiate_unary_anonymous_summand_at(
                    s_full.func.as_ref(),
                    s_full.end.as_ref(),
                )?
                else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &expected_tail,
                        tail,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum through e equals sum through e-1 plus last summand f(e)",
                )));
            }
        }
        Ok(None)
    }

    // product(s,e,f) = product(s,e-1,f) * f(e): same unary factor, shared start, e = (e-1)+1.
    pub(crate) fn try_verify_product_split_last_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        for (full_obj, mul_obj) in [(left, right), (right, left)] {
            let Obj::Product(p_full) = full_obj else {
                continue;
            };
            let Obj::Mul(m) = mul_obj else {
                continue;
            };
            for (prod_part, tail) in [
                (m.left.as_ref(), m.right.as_ref()),
                (m.right.as_ref(), m.left.as_ref()),
            ] {
                let Obj::Product(p_pre) = prod_part else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.start.as_ref(),
                        p_pre.start.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let end_pre_plus_one: Obj = Add::new((*p_pre.end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.func.as_ref(),
                        p_pre.func.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let Some(expected_tail) = self.instantiate_unary_anonymous_summand_at(
                    p_full.func.as_ref(),
                    p_full.end.as_ref(),
                )?
                else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &expected_tail,
                        tail,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: product through e equals product through e-1 times last factor f(e)",
                )));
            }
        }
        Ok(None)
    }

    pub(super) fn flatten_left_assoc_add_chain(obj: &Obj) -> Vec<&Obj> {
        match obj {
            Obj::Add(a) => {
                let mut v = Self::flatten_left_assoc_add_chain(a.left.as_ref());
                v.push(a.right.as_ref());
                v
            }
            _ => vec![obj],
        }
    }

    pub(super) fn flatten_left_assoc_mul_chain(obj: &Obj) -> Vec<&Obj> {
        match obj {
            Obj::Mul(m) => {
                let mut v = Self::flatten_left_assoc_mul_chain(m.left.as_ref());
                v.push(m.right.as_ref());
                v
            }
            _ => vec![obj],
        }
    }

    // sum(s,e,f) = sum(s1,e1,f) + sum(s2,e2,f) + ... with contiguous [si,ei] tiling [s,e], same unary f.
    pub(crate) fn try_verify_sum_partition_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        for (full_side, add_side) in [(left, right), (right, left)] {
            let Obj::Sum(s_full) = full_side else {
                continue;
            };
            let Obj::Add(_) = add_side else {
                continue;
            };
            let parts = Self::flatten_left_assoc_add_chain(add_side);
            if parts.len() < 2 {
                continue;
            }
            let mut sums: Vec<&Sum> = Vec::with_capacity(parts.len());
            let mut all_sum = true;
            for p in &parts {
                if let Obj::Sum(s) = p {
                    sums.push(s);
                } else {
                    all_sum = false;
                    break;
                }
            }
            if !all_sum {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s_full.start.as_ref(),
                    sums[0].start.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s_full.end.as_ref(),
                    sums[sums.len() - 1].end.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            let mut gaps_ok = true;
            for i in 0..sums.len().saturating_sub(1) {
                let gap = Add::new((*sums[i].end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &gap,
                        sums[i + 1].start.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    gaps_ok = false;
                    break;
                }
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for s in &sums {
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.func.as_ref(),
                        s.func.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    func_ok = false;
                    break;
                }
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: sum partitions closed range into adjacent sub-sums with the same summand",
            )));
        }
        Ok(None)
    }

    // product(s,e,f) = product(s1,e1,f) * product(s2,e2,f) * ... contiguous tiling, same unary f.
    pub(crate) fn try_verify_product_partition_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        for (full_side, mul_side) in [(left, right), (right, left)] {
            let Obj::Product(p_full) = full_side else {
                continue;
            };
            let Obj::Mul(_) = mul_side else {
                continue;
            };
            let parts = Self::flatten_left_assoc_mul_chain(mul_side);
            if parts.len() < 2 {
                continue;
            }
            let mut products: Vec<&Product> = Vec::with_capacity(parts.len());
            let mut all_prod = true;
            for p in &parts {
                if let Obj::Product(pr) = p {
                    products.push(pr);
                } else {
                    all_prod = false;
                    break;
                }
            }
            if !all_prod {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p_full.start.as_ref(),
                    products[0].start.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p_full.end.as_ref(),
                    products[products.len() - 1].end.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            let mut gaps_ok = true;
            for i in 0..products.len().saturating_sub(1) {
                let gap = Add::new((*products[i].end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &gap,
                        products[i + 1].start.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    gaps_ok = false;
                    break;
                }
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for p in &products {
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.func.as_ref(),
                        p.func.as_ref(),
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    func_ok = false;
                    break;
                }
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: product partitions closed range into adjacent sub-products with the same factor",
            )));
        }
        Ok(None)
    }

    /// `sum(L) = sum(R)` with `R` a translate of `L` by `k` on both bounds, reduced to pointwise
    /// equality on the right-hand index range.
    pub(crate) fn try_verify_sum_reindex_shift(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (l_obj, r_obj) in [(left, right), (right, left)] {
            let (Obj::Sum(l_sum), Obj::Sum(r_sum)) = (l_obj, r_obj) else {
                continue;
            };
            let direct_start_shift =
                direct_additive_range_shift(l_sum.start.as_ref(), r_sum.start.as_ref());
            let direct_end_shift =
                direct_additive_range_shift(l_sum.end.as_ref(), r_sum.end.as_ref());
            let (k, k_end) = match (direct_start_shift, direct_end_shift) {
                (Some(start_shift), Some(end_shift)) => (start_shift, end_shift),
                _ => (
                    Sub::new((*r_sum.start).clone(), (*l_sum.start).clone()).into(),
                    Sub::new((*r_sum.end).clone(), (*l_sum.end).clone()).into(),
                ),
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    &k,
                    &k_end,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            let y_name = self.generate_random_unused_name();
            let (y_binding, y_obj) = self.fresh_bound_param(y_name, ParamObjType::Forall)?;
            let normalized_k = evaluate_obj_to_exact_rational_obj_for_eval(&k).unwrap_or(k);
            let index_for_left = match &normalized_k {
                Obj::Number(number) => match number.normalized_value.parse::<i128>() {
                    Ok(0) => y_obj.clone(),
                    Ok(value) if value < 0 => Add::new(
                        y_obj.clone(),
                        Number::new(value.unsigned_abs().to_string()).into(),
                    )
                    .into(),
                    Ok(value) => {
                        Sub::new(y_obj.clone(), Number::new(value.to_string()).into()).into()
                    }
                    Err(_) => Sub::new(y_obj.clone(), normalized_k.clone()).into(),
                },
                _ => Sub::new(y_obj.clone(), normalized_k.clone()).into(),
            };
            let Some(at_l) =
                self.instantiate_unary_anonymous_summand_at(l_sum.func.as_ref(), &index_for_left)?
            else {
                continue;
            };
            let Some(at_r) =
                self.instantiate_unary_anonymous_summand_at(r_sum.func.as_ref(), &y_obj)?
            else {
                continue;
            };
            let then_fact: AtomicFact = EqualFact::new(at_l, at_r, line_file.clone()).into();
            let dom_lo: Fact =
                LessEqualFact::new((*r_sum.start).clone(), y_obj.clone(), line_file.clone()).into();
            let dom_hi: Fact =
                LessEqualFact::new(y_obj.clone(), (*r_sum.end).clone(), line_file.clone()).into();
            let r = self.verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
                y_binding,
                vec![dom_lo, dom_hi],
                &then_fact,
                builtin_state,
            )?;
            if r.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum reindexing (integer shift) from pointwise equality on the range",
                )));
            }
        }
        Ok(None)
    }

    /// `sum(s,e, \lambda x.c) = (e - s + 1) * c` when `c` does not mention the index parameter.
    pub(crate) fn try_verify_sum_constant_summand(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::Sum(s) = sum_side else {
                continue;
            };
            let af = match s.func.as_ref() {
                Obj::AnonymousFn(af) => af,
                Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => continue,
                },
                _ => continue,
            };
            if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
                continue;
            }
            let names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
            let pname = match names.first() {
                Some(n) => n.as_str(),
                None => continue,
            };
            if obj_expr_mentions_bare_id(af.equal_to.as_ref(), pname) {
                continue;
            }
            let c = (*af.equal_to).clone();
            let one: Obj = Number::new("1".to_string()).into();
            let count: Obj =
                Add::new(Sub::new((*s.end).clone(), (*s.start).clone()).into(), one).into();
            let m1: Obj = Mul::new(count.clone(), c.clone()).into();
            let m2: Obj = Mul::new(c, count).into();
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &m1,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
                || self
                    .verify_objs_are_equal_in_equality_builtin(
                        other,
                        &m2,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum of a constant summand over a closed integer range",
                )));
            }
        }
        Ok(None)
    }

    // Scalars factor out of finite sums over the same integer index range.
    // Example: `sum(m, n, fn(i Z) R {c * a(i)}) = c * sum(m, n, fn(i Z) R {a(i)})`.
    pub(crate) fn try_verify_sum_scalar_mul(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (sum_side, product_side) in [(left, right), (right, left)] {
            let Obj::Sum(sum) = sum_side else {
                continue;
            };
            let Obj::Mul(product) = product_side else {
                continue;
            };
            for (base_side, scalar) in [
                (product.left.as_ref(), product.right.as_ref()),
                (product.right.as_ref(), product.left.as_ref()),
            ] {
                let Obj::Sum(base_sum) = base_side else {
                    continue;
                };
                let start_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.start.as_ref(),
                    base_sum.start.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?;
                if !start_result.is_true() {
                    continue;
                }
                let end_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.end.as_ref(),
                    base_sum.end.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?;
                if !end_result.is_true() {
                    continue;
                }

                let x_name = self.generate_random_unused_name();
                let (x_binding, x_obj) = self.fresh_bound_param(x_name, ParamObjType::Forall)?;
                let Some(sum_inst) =
                    self.instantiate_unary_anonymous_summand_at(sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let Some(base_inst) =
                    self.instantiate_unary_anonymous_summand_at(base_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let expected: Obj = Mul::new(scalar.clone(), base_inst).into();
                let pointwise_fact: AtomicFact =
                    EqualFact::new(sum_inst, expected, line_file.clone()).into();
                let dom_lo: Fact =
                    LessEqualFact::new((*sum.start).clone(), x_obj.clone(), line_file.clone())
                        .into();
                let dom_hi: Fact =
                    LessEqualFact::new(x_obj.clone(), (*sum.end).clone(), line_file.clone()).into();
                let pointwise_result = self
                    .verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
                        x_binding,
                        vec![dom_lo, dom_hi],
                        &pointwise_fact,
                        builtin_state,
                    )?;
                if !pointwise_result.is_true() {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite sum scalar multiplication",
                )));
            }
        }
        Ok(None)
    }

    fn sum_functions_share_standard_additive_carrier(&self, functions: [&Obj; 3]) -> bool {
        functions.into_iter().all(|function| {
            let Some(body) = self.get_fn_range_function_body(function) else {
                return false;
            };
            matches!(
                body.ret_set.as_ref(),
                Obj::StandardSet(
                    StandardSet::NPos
                        | StandardSet::N
                        | StandardSet::Z
                        | StandardSet::ZNeg
                        | StandardSet::ZNz
                        | StandardSet::Q
                        | StandardSet::QPos
                        | StandardSet::QNeg
                        | StandardSet::QNz
                        | StandardSet::R
                        | StandardSet::RPos
                        | StandardSet::RNeg
                        | StandardSet::RNz
                        | StandardSet::C
                )
            )
        })
    }
}
