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
    pub fn try_verify_literal_zero_range_sum_is_zero(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
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
            equal_fact,
            "equality: a finite range sum of the literal zero function is zero",
        )))
    }

    /// `sum(s,e,f) = sum(s,e,g)` when `f(x) = g(x)` is known for every integer
    /// `x` in the shared closed range. Example: after proving
    /// `forall x Z: s <= x, x <= e => f(x) = g(x)`, the two sums are equal.
    pub fn try_verify_sum_pointwise_congruence(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let (Obj::Sum(left_sum), Obj::Sum(right_sum)) = (left, right) else {
            return Ok(None);
        };

        let Some(start_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(
                left_sum.start.as_ref(),
                right_sum.start.as_ref(),
                line_file.clone(),
            ),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(end_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(
                left_sum.end.as_ref(),
                right_sum.end.as_ref(),
                line_file.clone(),
            ),
            builtin_state,
        )?
        else {
            return Ok(None);
        };

        let unary_param_set = |func: &Obj| -> Option<Obj> {
            let af = match func {
                Obj::AnonymousFn(af) => af,
                Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(af) => af.as_ref(),
                    _ => return None,
                },
                _ => return None,
            };
            if af.body.set_bound_parameters.number_of_params() != 1
                || af.body.set_bound_parameters.len() != 1
            {
                return None;
            }
            Some(af.body.set_bound_parameters.as_slice()[0].set_obj().clone())
        };
        let (index_param_set, index_set_result) = match (
            unary_param_set(left_sum.func.as_ref()),
            unary_param_set(right_sum.func.as_ref()),
        ) {
            (Some(left_set), Some(right_set)) => {
                if let Some(result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(&left_set, &right_set, line_file.clone()),
                    builtin_state,
                )? {
                    (left_set, Some(result))
                } else {
                    (StandardSet::Z.into(), None)
                }
            }
            _ => (StandardSet::Z.into(), None),
        };

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
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

        let pointwise_fact: AtomicFact = self
            .new_equal_fact(left_value, right_value, line_file.clone())
            .into();
        let lower_bound: Fact = self
            .new_less_equal_fact((*left_sum.start).clone(), x_obj.clone(), line_file.clone())
            .into();
        let upper_bound: Fact = self
            .new_less_equal_fact(x_obj, (*left_sum.end).clone(), line_file.clone())
            .into();

        let pointwise_result = self.run_in_local_verification_env(
            builtin_state.verify_state(),
            |rt, local_verify_state| {
                let local_builtin_state = builtin_state.with_verify_state(local_verify_state);
                let params_def = TypedParameterList::new(vec![TypedParameterGroup::new(
                    vec![x_binding],
                    ParamType::Obj(index_param_set),
                )]);
                rt.define_params_with_type(&params_def, false, BindingScope::LocalBinder)?;
                rt.store_fact_without_forall_coverage_check_and_infer(lower_bound)?;
                rt.store_fact_without_forall_coverage_check_and_infer(upper_bound)?;

                let known_forall_result = rt.verify_atomic_fact_with_known_forall(
                    &pointwise_fact,
                    &local_verify_state.clone(),
                )?;
                if known_forall_result.is_success() {
                    return rt
                        .complete_atomic_fact_proof_result(
                            &pointwise_fact,
                            known_forall_result,
                            local_verify_state,
                        )
                        .map(Some);
                }
                rt.try_verify_atomic_fact_as_builtin_rule_premise(
                    &pointwise_fact,
                    &local_builtin_state,
                )
            },
        )?;
        let Some(pointwise_result) = pointwise_result else {
            return Ok(None);
        };

        let mut subgoals = vec![start_result, end_result];
        if let Some(index_set_result) = index_set_result {
            subgoals.push(index_set_result);
        }
        subgoals.push(pointwise_result);
        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(equal_fact, "equality: finite sums are congruent from pointwise equality on the shared integer range", subgoals)))
    }

    /// `sum(s,e,f) = sum(s,e,g) + sum(s,e,h)` when for all integer `x` with `s <= x <= e`,
    /// `f(x) = g(x) + h(x)` (summands are unary anonymous `fn` bodies, instantiated at `x`).
    pub fn try_verify_sum_additivity(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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

        let mut range_results = Vec::with_capacity(4);
        for (a, b) in [
            (sum_m.start.as_ref(), sum_a.start.as_ref()),
            (sum_m.start.as_ref(), sum_b.start.as_ref()),
            (sum_m.end.as_ref(), sum_a.end.as_ref()),
            (sum_m.end.as_ref(), sum_b.end.as_ref()),
        ] {
            let Some(result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(a, b, line_file.clone()),
                builtin_state,
            )?
            else {
                return Ok(None);
            };
            range_results.push(result);
        }

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;

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

        let then_fact: AtomicFact = self
            .new_equal_fact(l_inst, Add::new(a_inst, b_inst).into(), line_file.clone())
            .into();

        let dom_lo: Fact = self
            .new_less_equal_fact((*sum_m.start).clone(), x_obj.clone(), line_file.clone())
            .into();
        let dom_hi: Fact = self
            .new_less_equal_fact(x_obj.clone(), (*sum_m.end).clone(), line_file.clone())
            .into();

        let r = self.verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
            x_binding,
            vec![dom_lo, dom_hi],
            &then_fact,
            builtin_state,
        )?;
        let Some(r) = r else {
            return Ok(None);
        };
        range_results.push(r);
        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            equal_fact,
            "equality: sum additivity from pointwise equality on the integer index range",
            range_results,
        )))
    }

    /// Finite sums distribute over pointwise subtraction on the same integer range.
    /// Example: `sum(m,n,fn(i Z) R {f(i)-g(i)}) = sum(m,n,f) - sum(m,n,g)`.
    pub fn try_verify_sum_subtraction(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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

        let mut subgoals = Vec::with_capacity(5);
        for other_sum in [minuend_sum, subtrahend_sum] {
            for (a, b) in [
                (difference_sum.start.as_ref(), other_sum.start.as_ref()),
                (difference_sum.end.as_ref(), other_sum.end.as_ref()),
            ] {
                let Some(result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(a, b, line_file.clone()),
                    builtin_state,
                )?
                else {
                    return Ok(None);
                };
                subgoals.push(result);
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
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
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

        let dom_lo: Fact = self
            .new_less_equal_fact(
                (*difference_sum.start).clone(),
                x_obj.clone(),
                line_file.clone(),
            )
            .into();
        let dom_hi: Fact = self
            .new_less_equal_fact(x_obj, (*difference_sum.end).clone(), line_file.clone())
            .into();
        let dom_facts = vec![dom_lo, dom_hi];

        let expected: Obj = Sub::new(minuend_at_x, subtrahend_at_x).into();
        let pointwise_fact: AtomicFact = self
            .new_equal_fact(difference_at_x, expected, line_file.clone())
            .into();
        let pointwise_result = self
            .verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
                x_binding,
                dom_facts,
                &pointwise_fact,
                builtin_state,
            )?;
        let Some(pointwise_result) = pointwise_result else {
            return Ok(None);
        };
        subgoals.push(pointwise_result);

        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            equal_fact,
            "equality: finite sum subtraction over a common additive carrier",
            subgoals,
        )))
    }

    pub fn instantiate_unary_anonymous_summand_at(
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
        if SetBoundParameterGroup::number_of_params(&af.body.set_bound_parameters) != 1 {
            return Ok(None);
        }
        let param_defs = &af.body.set_bound_parameters;
        let args = vec![x.clone()];
        let param_to_arg_map =
            SetBoundParameterGroup::param_defs_and_args_to_param_to_arg_map(param_defs, &args);
        Ok(Some(self.inst_obj(
            af.equal_to.as_ref(),
            &param_to_arg_map,
            SubstitutionMode::Exact,
        )?))
    }

    pub fn verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
        &mut self,
        param_binding: SymbolBinding,
        dom_facts: Vec<Fact>,
        then_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<VerifyFactResult>, RuntimeError> {
        self.run_in_local_verification_env(
            builtin_state.verify_state(),
            |rt, local_verify_state| {
                let local_builtin_state = builtin_state.with_verify_state(local_verify_state);
                let params_def = TypedParameterList::new(vec![TypedParameterGroup::new(
                    vec![param_binding],
                    ParamType::Obj(StandardSet::Z.into()),
                )]);
                rt.define_params_with_type(&params_def, false, BindingScope::LocalBinder)?;
                for dom_fact in dom_facts {
                    rt.store_fact_without_forall_coverage_check_and_infer(dom_fact)?;
                }
                let known_forall_result = rt
                    .verify_atomic_fact_with_known_forall(then_fact, &local_verify_state.clone())?;
                if known_forall_result.is_success() {
                    return rt
                        .complete_atomic_fact_proof_result(
                            then_fact,
                            known_forall_result,
                            local_verify_state,
                        )
                        .map(Some);
                }
                rt.try_verify_atomic_fact_as_builtin_rule_premise(then_fact, &local_builtin_state)
            },
        )
    }

    /// `sum(a..b) + sum((b+1)..c) = sum(a..c)` with the same unary anonymous summand on each side.
    pub fn try_verify_sum_merge_adjacent_ranges(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
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
            if let Some(done) =
                self.try_verify_sum_merge_ordered_pair(equal_fact, a, b, s3, builtin_state)?
            {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    pub(super) fn try_verify_sum_merge_ordered_pair(
        &mut self,
        equal_fact: &EqualFact,
        s1: &Sum,
        s2: &Sum,
        s3: &Sum,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let line_file = &equal_fact.line_file;
        let one: Obj = Number::new("1".to_string()).into();
        let gap = Add::new((*s1.end).clone(), one).into();
        let Some(gap_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(&gap, s2.start.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(start_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(s1.start.as_ref(), s3.start.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(end_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(s2.end.as_ref(), s3.end.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(first_function_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(s1.func.as_ref(), s2.func.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(second_function_result) = self.try_verify_equal_fact_as_builtin_premise(
            &self.new_equal_fact_from_refs(s1.func.as_ref(), s3.func.as_ref(), line_file.clone()),
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
            equal_fact,
            "equality: merge adjacent sum ranges with the same summand",
            vec![
                gap_result,
                start_result,
                end_result,
                first_function_result,
                second_function_result,
            ],
        )))
    }

    // A finite sum over one index is the summand at that index.
    // Example: `sum(1, 1, fn(x N+) N+ {x}) = 1`.
    pub fn try_verify_sum_single_term(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        for (sum_obj, other) in [(left, right), (right, left)] {
            let Obj::Sum(sum) = sum_obj else {
                continue;
            };
            let Some(singleton_range_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    sum.start.as_ref(),
                    sum.end.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(expected) =
                self.instantiate_unary_function_at(sum.func.as_ref(), sum.start.as_ref())?
            else {
                continue;
            };
            let Some(value_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(&expected, other, line_file.clone()),
                builtin_state,
            )?
            else {
                continue;
            };
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "equality: single-term sum equals the summand".to_string(),
                    BuiltinRuleEvidence::Aggregate(AggregateBuiltinRule::SumSingle),
                    vec![singleton_range_result, value_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // A finite product over one index is the factor at that index.
    // Example: `product(1, 1, fn(x N+) N+ {x}) = 1`.
    pub fn try_verify_product_single_term(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        for (product_obj, other) in [(left, right), (right, left)] {
            let Obj::Product(product) = product_obj else {
                continue;
            };
            let Some(singleton_range_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    product.start.as_ref(),
                    product.end.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(expected) = self.instantiate_unary_anonymous_summand_at(
                product.func.as_ref(),
                product.start.as_ref(),
            )?
            else {
                continue;
            };
            let Some(value_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(&expected, other, line_file.clone()),
                builtin_state,
            )?
            else {
                continue;
            };
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: single-term product equals the factor",
                vec![singleton_range_result, value_result],
            )));
        }
        Ok(None)
    }

    // sum(s,e,f) = sum(s,e-1,f) + f(e): same unary summand, shared start, e = (e-1)+1 on the shorter range.
    pub fn try_verify_sum_split_last_term(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
                let Some(start_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        s_full.start.as_ref(),
                        s_pre.start.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let end_pre_plus_one: Obj = Add::new((*s_pre.end).clone(), one.clone()).into();
                let Some(end_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        s_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let Some(function_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        s_full.func.as_ref(),
                        s_pre.func.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let Some(expected_tail) =
                    self.instantiate_unary_function_at(s_full.func.as_ref(), s_full.end.as_ref())?
                else {
                    continue;
                };
                let Some(tail_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(&expected_tail, tail, line_file.clone()),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let ordered_range: AtomicFact = self
                    .new_less_equal_fact(
                        s_pre.start.as_ref().clone(),
                        s_pre.end.as_ref().clone(),
                        line_file.clone(),
                    )
                    .into();
                let Some(ordered_range_result) = self
                    .try_verify_atomic_fact_as_builtin_rule_premise(
                        &ordered_range,
                        builtin_state,
                    )?
                else {
                    continue;
                };
                return Ok(Some(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        equal_fact.clone().into(),
                        "equality: sum through e equals sum through e-1 plus last summand f(e)"
                            .to_string(),
                        BuiltinRuleEvidence::Aggregate(AggregateBuiltinRule::SumSplitLast),
                        vec![
                            start_result,
                            end_result,
                            function_result,
                            tail_result,
                            ordered_range_result,
                        ],
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // product(s,e,f) = product(s,e-1,f) * f(e): same unary factor, shared start, e = (e-1)+1.
    pub fn try_verify_product_split_last_term(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
                let Some(start_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        p_full.start.as_ref(),
                        p_pre.start.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let end_pre_plus_one: Obj = Add::new((*p_pre.end).clone(), one.clone()).into();
                let Some(end_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        p_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let Some(function_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        p_full.func.as_ref(),
                        p_pre.func.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let Some(expected_tail) = self.instantiate_unary_anonymous_summand_at(
                    p_full.func.as_ref(),
                    p_full.end.as_ref(),
                )?
                else {
                    continue;
                };
                let Some(tail_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(&expected_tail, tail, line_file.clone()),
                    builtin_state,
                )?
                else {
                    continue;
                };
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    equal_fact,
                    "equality: product through e equals product through e-1 times last factor f(e)",
                    vec![start_result, end_result, function_result, tail_result],
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
    pub fn try_verify_sum_partition_adjacent_ranges(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
            let Some(start_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    s_full.start.as_ref(),
                    sums[0].start.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(end_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    s_full.end.as_ref(),
                    sums[sums.len() - 1].end.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let mut subgoals = vec![start_result, end_result];
            let mut gaps_ok = true;
            for i in 0..sums.len().saturating_sub(1) {
                let gap = Add::new((*sums[i].end).clone(), one.clone()).into();
                let Some(gap_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        &gap,
                        sums[i + 1].start.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    gaps_ok = false;
                    break;
                };
                subgoals.push(gap_result);
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for s in &sums {
                let Some(function_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        s_full.func.as_ref(),
                        s.func.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    func_ok = false;
                    break;
                };
                subgoals.push(function_result);
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(equal_fact, "equality: sum partitions closed range into adjacent sub-sums with the same summand", subgoals)));
        }
        Ok(None)
    }

    // product(s,e,f) = product(s1,e1,f) * product(s2,e2,f) * ... contiguous tiling, same unary f.
    pub fn try_verify_product_partition_adjacent_ranges(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
            let Some(start_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    p_full.start.as_ref(),
                    products[0].start.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let Some(end_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(
                    p_full.end.as_ref(),
                    products[products.len() - 1].end.as_ref(),
                    line_file.clone(),
                ),
                builtin_state,
            )?
            else {
                continue;
            };
            let mut subgoals = vec![start_result, end_result];
            let mut gaps_ok = true;
            for i in 0..products.len().saturating_sub(1) {
                let gap = Add::new((*products[i].end).clone(), one.clone()).into();
                let Some(gap_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        &gap,
                        products[i + 1].start.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    gaps_ok = false;
                    break;
                };
                subgoals.push(gap_result);
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for p in &products {
                let Some(function_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        p_full.func.as_ref(),
                        p.func.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    func_ok = false;
                    break;
                };
                subgoals.push(function_result);
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(equal_fact, "equality: product partitions closed range into adjacent sub-products with the same factor", subgoals)));
        }
        Ok(None)
    }

    /// `sum(L) = sum(R)` with `R` a translate of `L` by `k` on both bounds, reduced to pointwise
    /// equality on the right-hand index range.
    pub fn try_verify_sum_reindex_shift(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
            let Some(shift_result) = self.try_verify_equal_fact_as_builtin_premise(
                &self.new_equal_fact_from_refs(&k, &k_end, line_file.clone()),
                builtin_state,
            )?
            else {
                continue;
            };
            let y_name = self.generate_random_unused_name();
            let (y_binding, y_obj) = self.fresh_bound_param(y_name)?;
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
            let then_fact: AtomicFact = self.new_equal_fact(at_l, at_r, line_file.clone()).into();
            let dom_lo: Fact = self
                .new_less_equal_fact((*r_sum.start).clone(), y_obj.clone(), line_file.clone())
                .into();
            let dom_hi: Fact = self
                .new_less_equal_fact(y_obj.clone(), (*r_sum.end).clone(), line_file.clone())
                .into();
            let r = self.verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
                y_binding,
                vec![dom_lo, dom_hi],
                &then_fact,
                builtin_state,
            )?;
            let Some(pointwise_result) = r else {
                continue;
            };
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: sum reindexing (integer shift) from pointwise equality on the range",
                vec![shift_result, pointwise_result],
            )));
        }
        Ok(None)
    }

    /// `sum(s,e, \lambda x.c) = (e - s + 1) * c` when `c` does not mention the index parameter.
    pub fn try_verify_sum_constant_summand(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
            if SetBoundParameterGroup::number_of_params(&af.body.set_bound_parameters) != 1 {
                continue;
            }
            let names = SetBoundParameterGroup::collect_param_names(&af.body.set_bound_parameters);
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
            let constant_result = if let Some(result) = self
                .try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(other, &m1, line_file.clone()),
                    builtin_state,
                )? {
                Some(result)
            } else {
                self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(other, &m2, line_file.clone()),
                    builtin_state,
                )?
            };
            let Some(constant_result) = constant_result else {
                continue;
            };
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                equal_fact,
                "equality: sum of a constant summand over a closed integer range",
                vec![constant_result],
            )));
        }
        Ok(None)
    }

    // Scalars factor out of finite sums over the same integer index range.
    // Example: `sum(m, n, fn(i Z) R {c * a(i)}) = c * sum(m, n, fn(i Z) R {a(i)})`.
    pub fn try_verify_sum_scalar_mul(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
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
                let Some(start_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        sum.start.as_ref(),
                        base_sum.start.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };
                let Some(end_result) = self.try_verify_equal_fact_as_builtin_premise(
                    &self.new_equal_fact_from_refs(
                        sum.end.as_ref(),
                        base_sum.end.as_ref(),
                        line_file.clone(),
                    ),
                    builtin_state,
                )?
                else {
                    continue;
                };

                let x_name = self.generate_random_unused_name();
                let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
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
                let pointwise_fact: AtomicFact = self
                    .new_equal_fact(sum_inst, expected, line_file.clone())
                    .into();
                let dom_lo: Fact = self
                    .new_less_equal_fact((*sum.start).clone(), x_obj.clone(), line_file.clone())
                    .into();
                let dom_hi: Fact = self
                    .new_less_equal_fact(x_obj.clone(), (*sum.end).clone(), line_file.clone())
                    .into();
                let pointwise_result = self
                    .verify_integer_pointwise_atomic_fact_by_known_forall_or_builtin(
                        x_binding,
                        vec![dom_lo, dom_hi],
                        &pointwise_fact,
                        builtin_state,
                    )?;
                let Some(pointwise_result) = pointwise_result else {
                    continue;
                };
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    equal_fact,
                    "equality: finite sum scalar multiplication",
                    vec![start_result, end_result, pointwise_result],
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
                        | StandardSet::ZStar
                        | StandardSet::Q
                        | StandardSet::QPos
                        | StandardSet::QNeg
                        | StandardSet::QStar
                        | StandardSet::R
                        | StandardSet::RPos
                        | StandardSet::RNeg
                        | StandardSet::RStar
                        | StandardSet::C
                )
            )
        })
    }
}
