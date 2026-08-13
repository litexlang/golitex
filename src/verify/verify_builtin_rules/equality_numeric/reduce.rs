use super::*;

const MAX_LITERAL_REDUCE_TERMS: u128 = 4096;

impl Runtime {
    /// The ordered fold of an empty closed interval is its seed.
    pub(crate) fn try_verify_reduce_empty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (reduce_side, other) in [(left, right), (right, left)] {
            let Obj::Reduce(reduce) = reduce_side else {
                continue;
            };
            let empty: AtomicFact = LessFact::new(
                reduce.end.as_ref().clone(),
                reduce.start.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            if !self
                .verify_builtin_rule_premise(&empty, builtin_state)?
                .is_true()
            {
                continue;
            }
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    reduce.seed.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: reduce over an empty closed interval returns its seed",
                )));
            }
        }
        Ok(None)
    }

    /// Expand a bounded literal integer interval as the specified ascending
    /// left fold. Example: `reduce(1,3,f,op,s)` becomes
    /// `op(op(op(s,f(1)),f(2)),f(3))`.
    pub(crate) fn try_verify_reduce_literal_expansion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (reduce_side, other) in [(left, right), (right, left)] {
            let Obj::Reduce(reduce) = reduce_side else {
                continue;
            };
            let Some((start, end)) = self.literal_reduce_integer_bounds(reduce) else {
                continue;
            };
            if end < start {
                continue;
            }
            let Some(term_count) = end
                .checked_sub(start)
                .and_then(|distance| distance.checked_add(1))
                .map(|count| count as u128)
            else {
                continue;
            };
            if term_count > MAX_LITERAL_REDUCE_TERMS {
                continue;
            }

            let mut accumulator = reduce.seed.as_ref().clone();
            for index in start..=end {
                let index_obj: Obj = Number::new(index.to_string()).into();
                let Some(value) =
                    self.instantiate_reduce_function_at(reduce.func.as_ref(), &[index_obj])?
                else {
                    return Ok(None);
                };
                let Some(next) =
                    self.instantiate_reduce_function_at(reduce.op.as_ref(), &[accumulator, value])?
                else {
                    return Ok(None);
                };
                accumulator = next;
            }
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &accumulator,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: literal reduce expands as an ascending left fold",
                )));
            }
        }
        Ok(None)
    }

    fn literal_reduce_integer_bounds(&self, reduce: &Reduce) -> Option<(i128, i128)> {
        let start = self.resolve_obj_to_number(reduce.start.as_ref())?;
        let end = self.resolve_obj_to_number(reduce.end.as_ref())?;
        let start_text = start.normalized_value.trim();
        let end_text = end.normalized_value.trim();
        if !is_number_string_literally_integer_without_dot(start_text.to_string())
            || !is_number_string_literally_integer_without_dot(end_text.to_string())
        {
            return None;
        }
        Some((start_text.parse().ok()?, end_text.parse().ok()?))
    }

    /// Recursive defining equation for a nonempty ordered fold.
    pub(crate) fn try_verify_reduce_step(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (reduce_side, other) in [(left, right), (right, left)] {
            let Obj::Reduce(reduce) = reduce_side else {
                continue;
            };
            let nonempty: AtomicFact = LessEqualFact::new(
                reduce.start.as_ref().clone(),
                reduce.end.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            if !self
                .verify_builtin_rule_premise(&nonempty, builtin_state)?
                .is_true()
            {
                continue;
            }
            let previous_end: Obj = Sub::new(
                reduce.end.as_ref().clone(),
                Number::new("1".to_string()).into(),
            )
            .into();
            let previous: Obj = Reduce::new(
                reduce.start.as_ref().clone(),
                previous_end,
                reduce.func.as_ref().clone(),
                reduce.op.as_ref().clone(),
                reduce.seed.as_ref().clone(),
            )
            .into();
            let Some(last_value) = self.instantiate_reduce_function_at(
                reduce.func.as_ref(),
                &[reduce.end.as_ref().clone()],
            )?
            else {
                continue;
            };
            let Some(expected) =
                self.instantiate_reduce_function_at(reduce.op.as_ref(), &[previous, last_value])?
            else {
                continue;
            };
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &expected,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: nonempty reduce satisfies its last-step equation",
                )));
            }
        }
        Ok(None)
    }

    pub(crate) fn try_verify_finite_set_reduce_empty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let empty_set: Obj = ListSet::new(Vec::new()).into();
        for (reduce_side, other) in [(left, right), (right, left)] {
            let Obj::FiniteSetReduce(reduce) = reduce_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    reduce.set.as_ref(),
                    &empty_set,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                continue;
            }
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    reduce.seed.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite_set_reduce over the empty set returns its seed",
                )));
            }
        }
        Ok(None)
    }

    /// A displayed finite set is folded from the seed in display order. The
    /// well-definedness gate has already established associativity and
    /// commutativity, so this order is only an evaluation witness, not syntax
    /// with mathematical significance.
    pub(crate) fn try_verify_finite_set_reduce_list_expansion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (reduce_side, other) in [(left, right), (right, left)] {
            let Obj::FiniteSetReduce(reduce) = reduce_side else {
                continue;
            };
            let mut list_sets = Vec::new();
            match reduce.set.as_ref() {
                Obj::ListSet(list) => list_sets.push(list.clone()),
                set => {
                    for representative in self.get_all_obj_representatives_equal_to_given(set) {
                        if let Obj::ListSet(list) = representative {
                            list_sets.push(list);
                        }
                    }
                }
            }
            for list in list_sets {
                let mut accumulator = reduce.seed.as_ref().clone();
                let mut complete = true;
                for element in &list.list {
                    let Some(value) = self.instantiate_reduce_function_at(
                        reduce.func.as_ref(),
                        &[element.as_ref().clone()],
                    )?
                    else {
                        complete = false;
                        break;
                    };
                    let Some(next) = self.instantiate_reduce_function_at(
                        reduce.op.as_ref(),
                        &[accumulator.clone(), value],
                    )?
                    else {
                        complete = false;
                        break;
                    };
                    accumulator = next;
                }
                if !complete {
                    continue;
                }
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        other,
                        &accumulator,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: finite_set_reduce expands through a finite-set enumeration",
                    )));
                }
            }
        }
        Ok(None)
    }

    pub(crate) fn try_verify_finite_set_reduce_closed_range_bridge(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (finite_side, other) in [(left, right), (right, left)] {
            let Obj::FiniteSetReduce(finite) = finite_side else {
                continue;
            };
            let Obj::ClosedRange(range) = finite.set.as_ref() else {
                continue;
            };
            let expected: Obj = Reduce::new(
                range.start.as_ref().clone(),
                range.end.as_ref().clone(),
                finite.func.as_ref().clone(),
                finite.op.as_ref().clone(),
                finite.seed.as_ref().clone(),
            )
            .into();
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &expected,
                    line_file.clone(),
                    builtin_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite_set_reduce over a closed range uses its ascending enumeration",
                )));
            }
        }
        Ok(None)
    }

    /// Inserting one fresh element contributes exactly one new value. The
    /// operation-law gate makes the chosen side/order immaterial.
    pub(crate) fn try_verify_finite_set_reduce_fresh_insertion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (union_side, other) in [(left, right), (right, left)] {
            let Obj::FiniteSetReduce(union_reduce) = union_side else {
                continue;
            };
            let Obj::Union(union) = union_reduce.set.as_ref() else {
                continue;
            };
            for (singleton_side, smaller_set) in [
                (union.left.as_ref(), union.right.as_ref()),
                (union.right.as_ref(), union.left.as_ref()),
            ] {
                let Obj::ListSet(singleton) = singleton_side else {
                    continue;
                };
                let [inserted] = singleton.list.as_slice() else {
                    continue;
                };
                let freshness: AtomicFact = NotInFact::new(
                    inserted.as_ref().clone(),
                    smaller_set.clone(),
                    line_file.clone(),
                )
                .into();
                if !self
                    .verify_builtin_rule_premise(&freshness, builtin_state)?
                    .is_true()
                {
                    continue;
                }
                let smaller: Obj = FiniteSetReduce::new(
                    smaller_set.clone(),
                    union_reduce.func.as_ref().clone(),
                    union_reduce.op.as_ref().clone(),
                    union_reduce.seed.as_ref().clone(),
                )
                .into();
                let Some(value) = self.instantiate_reduce_function_at(
                    union_reduce.func.as_ref(),
                    &[inserted.as_ref().clone()],
                )?
                else {
                    continue;
                };
                let Some(expected) = self
                    .instantiate_reduce_function_at(union_reduce.op.as_ref(), &[value, smaller])?
                else {
                    continue;
                };
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        other,
                        &expected,
                        line_file.clone(),
                        builtin_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: finite_set_reduce after inserting a fresh element",
                    )));
                }
            }
        }
        Ok(None)
    }

    /// Addition with seed zero and multiplication with seed one specialize a
    /// range reduction to the existing `sum` and `product` objects.
    /// Example: `reduce(a,b,f,add,0) = sum(a,b,f)`.
    pub(crate) fn try_verify_reduce_specialized_aggregate_bridge(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (reduce_side, aggregate_side) in [(left, right), (right, left)] {
            let Obj::Reduce(reduce) = reduce_side else {
                continue;
            };
            match aggregate_side {
                Obj::Sum(sum) => {
                    let Some(subgoals) = self.verify_reduce_range_specialization(
                        reduce,
                        sum.start.as_ref(),
                        sum.end.as_ref(),
                        sum.func.as_ref(),
                        NativeReduceSpecialization::Additive,
                        line_file.clone(),
                        builtin_state,
                    )?
                    else {
                        continue;
                    };
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        left,
                        right,
                        line_file,
                        "equality: additive reduce with seed zero equals range sum",
                        subgoals,
                    )));
                }
                Obj::Product(product) => {
                    let Some(subgoals) = self.verify_reduce_range_specialization(
                        reduce,
                        product.start.as_ref(),
                        product.end.as_ref(),
                        product.func.as_ref(),
                        NativeReduceSpecialization::Multiplicative,
                        line_file.clone(),
                        builtin_state,
                    )?
                    else {
                        continue;
                    };
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        left,
                        right,
                        line_file,
                        "equality: multiplicative reduce with seed one equals range product",
                        subgoals,
                    )));
                }
                _ => {}
            }
        }
        Ok(None)
    }

    /// Addition with seed zero and multiplication with seed one specialize a
    /// finite-set reduction to the existing finite-set aggregates.
    /// Example: `finite_set_reduce(S,f,add,0) = finite_set_sum(S,f)`.
    pub(crate) fn try_verify_finite_set_reduce_specialized_aggregate_bridge(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (reduce_side, aggregate_side) in [(left, right), (right, left)] {
            let Obj::FiniteSetReduce(reduce) = reduce_side else {
                continue;
            };
            match aggregate_side {
                Obj::SumOfFiniteSet(sum) => {
                    let Some(subgoals) = self.verify_finite_set_reduce_specialization(
                        reduce,
                        sum.set.as_ref(),
                        sum.func.as_ref(),
                        NativeReduceSpecialization::Additive,
                        line_file.clone(),
                        builtin_state,
                    )?
                    else {
                        continue;
                    };
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        left,
                        right,
                        line_file,
                        "equality: additive finite_set_reduce with seed zero equals finite_set_sum",
                        subgoals,
                    )));
                }
                Obj::ProductOfFiniteSet(product) => {
                    let Some(subgoals) = self.verify_finite_set_reduce_specialization(
                        reduce,
                        product.set.as_ref(),
                        product.func.as_ref(),
                        NativeReduceSpecialization::Multiplicative,
                        line_file.clone(),
                        builtin_state,
                    )?
                    else {
                        continue;
                    };
                    return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                        left,
                        right,
                        line_file,
                        "equality: multiplicative finite_set_reduce with seed one equals finite_set_product",
                        subgoals,
                    )));
                }
                _ => {}
            }
        }
        Ok(None)
    }

    /// Reductions are congruent when their structural parameters agree and
    /// their unary functions are pointwise equal on the exact index set.
    /// Examples use `$fn_eq_in(f,g,a...b)` or `$fn_eq_in(f,g,S)`.
    pub(crate) fn try_verify_reduce_pointwise_congruence(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        match (left, right) {
            (Obj::Reduce(left_reduce), Obj::Reduce(right_reduce)) => {
                let mut subgoals = Vec::new();
                for (left_arg, right_arg) in [
                    (left_reduce.start.as_ref(), right_reduce.start.as_ref()),
                    (left_reduce.end.as_ref(), right_reduce.end.as_ref()),
                    (left_reduce.op.as_ref(), right_reduce.op.as_ref()),
                    (left_reduce.seed.as_ref(), right_reduce.seed.as_ref()),
                ] {
                    let result = self.verify_objs_are_equal_in_equality_builtin(
                        left_arg,
                        right_arg,
                        line_file.clone(),
                        builtin_state,
                    )?;
                    if !result.is_true() {
                        return Ok(None);
                    }
                    subgoals.extend(equality_builtin_match_subgoals(left_arg, right_arg, result));
                }
                let index_set: Obj = ClosedRange::new(
                    left_reduce.start.as_ref().clone(),
                    left_reduce.end.as_ref().clone(),
                )
                .into();
                let pointwise = self.verify_reduce_functions_pointwise_on_set(
                    left_reduce.func.as_ref(),
                    right_reduce.func.as_ref(),
                    &index_set,
                    line_file.clone(),
                    builtin_state,
                )?;
                if !pointwise.is_true() {
                    return Ok(None);
                }
                subgoals.push(pointwise);
                Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: reduce congruence from pointwise equality on the closed range",
                    subgoals,
                )))
            }
            (Obj::FiniteSetReduce(left_reduce), Obj::FiniteSetReduce(right_reduce)) => {
                let mut subgoals = Vec::new();
                for (left_arg, right_arg) in [
                    (left_reduce.set.as_ref(), right_reduce.set.as_ref()),
                    (left_reduce.op.as_ref(), right_reduce.op.as_ref()),
                    (left_reduce.seed.as_ref(), right_reduce.seed.as_ref()),
                ] {
                    let result = self.verify_objs_are_equal_in_equality_builtin(
                        left_arg,
                        right_arg,
                        line_file.clone(),
                        builtin_state,
                    )?;
                    if !result.is_true() {
                        return Ok(None);
                    }
                    subgoals.extend(equality_builtin_match_subgoals(left_arg, right_arg, result));
                }
                let pointwise = self.verify_reduce_functions_pointwise_on_set(
                    left_reduce.func.as_ref(),
                    right_reduce.func.as_ref(),
                    left_reduce.set.as_ref(),
                    line_file.clone(),
                    builtin_state,
                )?;
                if !pointwise.is_true() {
                    return Ok(None);
                }
                subgoals.push(pointwise);
                Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: finite_set_reduce congruence from fn_eq_in on the finite set",
                    subgoals,
                )))
            }
            _ => Ok(None),
        }
    }

    /// An ordered reduction is invariant under translating its closed integer
    /// interval when the pulled-back function supplies the same values in the
    /// same order. No associativity or commutativity is required.
    /// Example: `reduce(a,b,f,op,s) = reduce(0,b-a,fn(k Z) T {f(a+k)},op,s)`.
    pub(crate) fn try_verify_reduce_order_preserving_translation(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (source_side, translated_side) in [(left, right), (right, left)] {
            let (Obj::Reduce(source), Obj::Reduce(translated)) = (source_side, translated_side)
            else {
                continue;
            };

            let mut subgoals = Vec::new();
            let mut structural_match = true;
            for (actual, expected) in [
                (source.op.as_ref(), translated.op.as_ref()),
                (source.seed.as_ref(), translated.seed.as_ref()),
            ] {
                let result = self.verify_objs_are_equal_in_equality_builtin(
                    actual,
                    expected,
                    line_file.clone(),
                    builtin_state,
                )?;
                if !result.is_true() {
                    structural_match = false;
                    break;
                }
                subgoals.extend(equality_builtin_match_subgoals(actual, expected, result));
            }
            if !structural_match {
                continue;
            }

            let source_length: Obj =
                Sub::new(source.end.as_ref().clone(), source.start.as_ref().clone()).into();
            let translated_length: Obj = Sub::new(
                translated.end.as_ref().clone(),
                translated.start.as_ref().clone(),
            )
            .into();
            let length_result = self.verify_objs_are_equal_in_equality_builtin(
                &source_length,
                &translated_length,
                line_file.clone(),
                builtin_state,
            )?;
            if !length_result.is_true() {
                continue;
            }
            subgoals.extend(equality_builtin_match_subgoals(
                &source_length,
                &translated_length,
                length_result,
            ));

            let nonempty: AtomicFact = LessEqualFact::new(
                source.start.as_ref().clone(),
                source.end.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            let nonempty_result = self.verify_builtin_rule_premise(&nonempty, builtin_state)?;
            if !nonempty_result.is_true() {
                let empty: AtomicFact = LessFact::new(
                    source.end.as_ref().clone(),
                    source.start.as_ref().clone(),
                    line_file.clone(),
                )
                .into();
                let empty_result = self.verify_builtin_rule_premise(&empty, builtin_state)?;
                if !empty_result.is_true() {
                    continue;
                }
                subgoals.push(empty_result);
                return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                    left,
                    right,
                    line_file,
                    "equality: reduce substitution translates equally long empty intervals",
                    subgoals,
                )));
            }
            subgoals.push(nonempty_result);

            let source_func = source.func.as_ref().clone();
            let translated_func = translated.func.as_ref().clone();
            let source_start = source.start.as_ref().clone();
            let translated_start = translated.start.as_ref().clone();
            let translated_set: Obj = ClosedRange::new(
                translated.start.as_ref().clone(),
                translated.end.as_ref().clone(),
            )
            .into();
            let pointwise_result = self.run_in_local_env(|rt| {
                let index_name = rt.generate_random_unused_name();
                let (index_binding, index) =
                    rt.fresh_bound_param(index_name, ParamObjType::Forall)?;
                let params = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![index_binding],
                    ParamType::Obj(translated_set),
                )]);
                rt.define_params_with_type(&params, false, ParamObjType::Forall)?;

                let offset: Obj = Sub::new(index.clone(), translated_start).into();
                let source_index: Obj = Add::new(source_start, offset).into();
                let Some(source_value) =
                    rt.instantiate_reduce_function_at(&source_func, &[source_index])?
                else {
                    return Ok(StmtUnknown::new().into());
                };
                let Some(translated_value) =
                    rt.instantiate_reduce_function_at(&translated_func, &[index])?
                else {
                    return Ok(StmtUnknown::new().into());
                };
                let equality: AtomicFact =
                    EqualFact::new(source_value, translated_value, line_file.clone()).into();
                let known_forall = rt.verify_atomic_fact_with_known_forall(
                    &equality,
                    &UseContextVerifyState::new(0, true),
                )?;
                if known_forall.is_true() {
                    return Ok(known_forall);
                }
                rt.verify_builtin_rule_premise(&equality, builtin_state)
            })?;
            if !pointwise_result.is_true() {
                continue;
            }
            subgoals.push(pointwise_result);

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: reduce substitution by an order-preserving interval translation",
                subgoals,
            )));
        }
        Ok(None)
    }

    /// A nonempty ordered reduction may consume its first value into the seed
    /// and continue at the next integer, without any operation laws.
    /// Example: `reduce(a,b,f,op,s) = reduce(a+1,b,f,op,op(s,f(a)))`.
    pub(crate) fn try_verify_reduce_first_step(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (full_side, tail_side) in [(left, right), (right, left)] {
            let (Obj::Reduce(full), Obj::Reduce(tail)) = (full_side, tail_side) else {
                continue;
            };
            let one: Obj = Number::new("1".to_string()).into();
            let expected_tail_start: Obj = Add::new(full.start.as_ref().clone(), one).into();

            let mut subgoals = Vec::new();
            let mut structural_match = true;
            for (actual, expected) in [
                (tail.start.as_ref(), &expected_tail_start),
                (tail.end.as_ref(), full.end.as_ref()),
                (tail.func.as_ref(), full.func.as_ref()),
                (tail.op.as_ref(), full.op.as_ref()),
            ] {
                let result = self.verify_objs_are_equal_in_equality_builtin(
                    actual,
                    expected,
                    line_file.clone(),
                    builtin_state,
                )?;
                if !result.is_true() {
                    structural_match = false;
                    break;
                }
                subgoals.extend(equality_builtin_match_subgoals(actual, expected, result));
            }
            if !structural_match {
                continue;
            }

            let nonempty: AtomicFact = LessEqualFact::new(
                full.start.as_ref().clone(),
                full.end.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            let nonempty_result = self.verify_builtin_rule_premise(&nonempty, builtin_state)?;
            if !nonempty_result.is_true() {
                continue;
            }
            subgoals.push(nonempty_result);

            let Some(first_value) = self.instantiate_reduce_function_at(
                full.func.as_ref(),
                &[full.start.as_ref().clone()],
            )?
            else {
                continue;
            };
            let Some(expected_seed) = self.instantiate_reduce_function_at(
                full.op.as_ref(),
                &[full.seed.as_ref().clone(), first_value],
            )?
            else {
                continue;
            };
            let seed_result = self.verify_objs_are_equal_in_equality_builtin(
                tail.seed.as_ref(),
                &expected_seed,
                line_file.clone(),
                builtin_state,
            )?;
            if !seed_result.is_true() {
                continue;
            }
            subgoals.extend(equality_builtin_match_subgoals(
                tail.seed.as_ref(),
                &expected_seed,
                seed_result,
            ));

            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: nonempty reduce consumes its first value into the seed",
                subgoals,
            )));
        }
        Ok(None)
    }

    /// An ordered reduction can be resumed on the immediately adjacent tail,
    /// preserving order even for noncommutative operations.
    /// Example: `reduce(a,c,f,op,s) = reduce(b+1,c,f,op,reduce(a,b,f,op,s))`.
    pub(crate) fn try_verify_reduce_adjacent_partition(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (full_side, resumed_side) in [(left, right), (right, left)] {
            let (Obj::Reduce(full), Obj::Reduce(tail)) = (full_side, resumed_side) else {
                continue;
            };
            let Obj::Reduce(prefix) = tail.seed.as_ref() else {
                continue;
            };
            let one: Obj = Number::new("1".to_string()).into();
            let expected_tail_start: Obj = Add::new(prefix.end.as_ref().clone(), one).into();
            let mut subgoals = Vec::new();
            let mut structural_match = true;
            for (actual, expected) in [
                (full.start.as_ref(), prefix.start.as_ref()),
                (full.end.as_ref(), tail.end.as_ref()),
                (tail.start.as_ref(), &expected_tail_start),
                (full.func.as_ref(), prefix.func.as_ref()),
                (full.func.as_ref(), tail.func.as_ref()),
                (full.op.as_ref(), prefix.op.as_ref()),
                (full.op.as_ref(), tail.op.as_ref()),
                (full.seed.as_ref(), prefix.seed.as_ref()),
            ] {
                let result = self.verify_objs_are_equal_in_equality_builtin(
                    actual,
                    expected,
                    line_file.clone(),
                    builtin_state,
                )?;
                if !result.is_true() {
                    structural_match = false;
                    break;
                }
                subgoals.extend(equality_builtin_match_subgoals(actual, expected, result));
            }
            if !structural_match {
                continue;
            }
            let prefix_nonempty: AtomicFact = LessEqualFact::new(
                full.start.as_ref().clone(),
                prefix.end.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            let prefix_result =
                self.verify_builtin_rule_premise(&prefix_nonempty, builtin_state)?;
            if !prefix_result.is_true() {
                continue;
            }
            let tail_nonempty: AtomicFact = LessFact::new(
                prefix.end.as_ref().clone(),
                full.end.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            let tail_result = self.verify_builtin_rule_premise(&tail_nonempty, builtin_state)?;
            if !tail_result.is_true() {
                continue;
            }
            subgoals.push(prefix_result);
            subgoals.push(tail_result);
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: reduce partitions into adjacent ordered ranges",
                subgoals,
            )));
        }
        Ok(None)
    }

    /// A finite-set reduction over a disjoint union is a reduction of either
    /// part seeded by the reduction of the other part. This form is valid even
    /// when `seed` is not an identity.
    /// Example: `F(union(A,B),s) = F(A,F(B,s))` when `intersect(A,B) = {}`.
    pub(crate) fn try_verify_finite_set_reduce_disjoint_union(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (full_side, nested_side) in [(left, right), (right, left)] {
            let (Obj::FiniteSetReduce(full), Obj::FiniteSetReduce(outer)) =
                (full_side, nested_side)
            else {
                continue;
            };
            let Obj::FiniteSetReduce(inner) = outer.seed.as_ref() else {
                continue;
            };
            let expected_union: Obj =
                Union::new(outer.set.as_ref().clone(), inner.set.as_ref().clone()).into();
            let union_result = self.verify_objs_are_equal_in_equality_builtin(
                full.set.as_ref(),
                &expected_union,
                line_file.clone(),
                builtin_state,
            )?;
            if !union_result.is_true() {
                continue;
            }
            let mut subgoals =
                equality_builtin_match_subgoals(full.set.as_ref(), &expected_union, union_result);
            let empty_set: Obj = ListSet::new(Vec::new()).into();
            let intersection: Obj =
                Intersect::new(outer.set.as_ref().clone(), inner.set.as_ref().clone()).into();
            let disjoint_result = self.verify_objs_are_equal_in_equality_builtin(
                &intersection,
                &empty_set,
                line_file.clone(),
                builtin_state,
            )?;
            if !disjoint_result.is_true() {
                continue;
            }
            subgoals.push(disjoint_result);
            let mut structural_match = true;
            for (actual, expected) in [
                (full.op.as_ref(), outer.op.as_ref()),
                (full.op.as_ref(), inner.op.as_ref()),
                (full.seed.as_ref(), inner.seed.as_ref()),
            ] {
                let result = self.verify_objs_are_equal_in_equality_builtin(
                    actual,
                    expected,
                    line_file.clone(),
                    builtin_state,
                )?;
                if !result.is_true() {
                    structural_match = false;
                    break;
                }
                subgoals.extend(equality_builtin_match_subgoals(actual, expected, result));
            }
            if !structural_match {
                continue;
            }
            let outer_pointwise = self.verify_reduce_functions_pointwise_on_set(
                full.func.as_ref(),
                outer.func.as_ref(),
                outer.set.as_ref(),
                line_file.clone(),
                builtin_state,
            )?;
            if !outer_pointwise.is_true() {
                continue;
            }
            let inner_pointwise = self.verify_reduce_functions_pointwise_on_set(
                full.func.as_ref(),
                inner.func.as_ref(),
                inner.set.as_ref(),
                line_file.clone(),
                builtin_state,
            )?;
            if !inner_pointwise.is_true() {
                continue;
            }
            subgoals.push(outer_pointwise);
            subgoals.push(inner_pointwise);
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: finite_set_reduce over a disjoint union preserves the single seed",
                subgoals,
            )));
        }
        Ok(None)
    }

    /// A commutative finite-set reduction is invariant under a known
    /// bijective reindexing. Example: `$bijective(Y,X,g)` transports
    /// `F(X,f)` to `F(Y,fn(y Y) T {f(g(y))})`.
    pub(crate) fn try_verify_finite_set_reduce_bijective_reindexing(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (source_side, pullback_side) in [(left, right), (right, left)] {
            let (Obj::FiniteSetReduce(source), Obj::FiniteSetReduce(pullback)) =
                (source_side, pullback_side)
            else {
                continue;
            };
            let op_result = self.verify_objs_are_equal_in_equality_builtin(
                source.op.as_ref(),
                pullback.op.as_ref(),
                line_file.clone(),
                builtin_state,
            )?;
            if !op_result.is_true() {
                continue;
            }
            let seed_result = self.verify_objs_are_equal_in_equality_builtin(
                source.seed.as_ref(),
                pullback.seed.as_ref(),
                line_file.clone(),
                builtin_state,
            )?;
            if !seed_result.is_true() {
                continue;
            }

            let y_name = self.generate_random_unused_name();
            let (y_binding, y_obj) = self.fresh_bound_param(y_name, ParamObjType::Forall)?;
            let Some(pullback_at_y) =
                self.instantiate_reduce_function_at(pullback.func.as_ref(), &[y_obj.clone()])?
            else {
                continue;
            };
            let Some(map_y) =
                Self::unary_application_arg_matching_callable(&pullback_at_y, source.func.as_ref())
            else {
                continue;
            };
            let Some(source_at_map_y) =
                self.instantiate_reduce_function_at(source.func.as_ref(), &[map_y.clone()])?
            else {
                continue;
            };
            let pointwise_fact: AtomicFact =
                EqualFact::new(pullback_at_y, source_at_map_y, line_file.clone()).into();
            let pointwise_result = self.run_in_local_env(|rt| {
                let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![y_binding],
                    ParamType::Obj(pullback.set.as_ref().clone()),
                )]);
                rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
                let known_forall = rt.verify_atomic_fact_with_known_forall(
                    &pointwise_fact,
                    &UseContextVerifyState::new(0, true),
                )?;
                if known_forall.is_true() {
                    return Ok(known_forall);
                }
                rt.verify_builtin_rule_premise(&pointwise_fact, builtin_state)
            })?;
            if !pointwise_result.is_true() {
                continue;
            }
            let Obj::FnObj(map_call) = map_y else {
                continue;
            };
            let map: Obj = map_call.head.as_ref().clone().into();
            if !self.has_known_builtin_bijection(
                pullback.set.as_ref(),
                source.set.as_ref(),
                &map,
                line_file.clone(),
                builtin_state,
            )? {
                continue;
            }
            let mut subgoals = Vec::new();
            subgoals.extend(equality_builtin_match_subgoals(
                source.op.as_ref(),
                pullback.op.as_ref(),
                op_result,
            ));
            subgoals.extend(equality_builtin_match_subgoals(
                source.seed.as_ref(),
                pullback.seed.as_ref(),
                seed_result,
            ));
            subgoals.push(pointwise_result);
            return Ok(Some(factual_equal_success_by_builtin_reason_with_subgoals(
                left,
                right,
                line_file,
                "equality: finite_set_reduce substitution along a bijection",
                subgoals,
            )));
        }
        Ok(None)
    }

    fn verify_reduce_range_specialization(
        &mut self,
        reduce: &Reduce,
        aggregate_start: &Obj,
        aggregate_end: &Obj,
        aggregate_func: &Obj,
        specialization: NativeReduceSpecialization,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut subgoals = Vec::new();
        for (actual, expected) in [
            (reduce.start.as_ref(), aggregate_start),
            (reduce.end.as_ref(), aggregate_end),
        ] {
            let result = self.verify_objs_are_equal_in_equality_builtin(
                actual,
                expected,
                line_file.clone(),
                builtin_state,
            )?;
            if !result.is_true() {
                return Ok(None);
            }
            subgoals.extend(equality_builtin_match_subgoals(actual, expected, result));
        }
        let index_set: Obj =
            ClosedRange::new(aggregate_start.clone(), aggregate_end.clone()).into();
        let function_result = self.verify_reduce_functions_pointwise_on_set(
            reduce.func.as_ref(),
            aggregate_func,
            &index_set,
            line_file.clone(),
            builtin_state,
        )?;
        if !function_result.is_true() {
            return Ok(None);
        }
        subgoals.push(function_result);
        let identity = specialization.identity();
        let seed_result = self.verify_objs_are_equal_in_equality_builtin(
            reduce.seed.as_ref(),
            &identity,
            line_file.clone(),
            builtin_state,
        )?;
        if !seed_result.is_true() {
            return Ok(None);
        }
        subgoals.extend(equality_builtin_match_subgoals(
            reduce.seed.as_ref(),
            &identity,
            seed_result,
        ));
        let Some(carrier) = self.reduce_carrier_from_operation(reduce.op.as_ref()) else {
            return Ok(None);
        };
        let operation_result = self.verify_reduce_operation_matches_native(
            reduce.op.as_ref(),
            &carrier,
            specialization,
            line_file,
            builtin_state,
        )?;
        if !operation_result.is_true() {
            return Ok(None);
        }
        subgoals.push(operation_result);
        Ok(Some(subgoals))
    }

    fn verify_finite_set_reduce_specialization(
        &mut self,
        reduce: &FiniteSetReduce,
        aggregate_set: &Obj,
        aggregate_func: &Obj,
        specialization: NativeReduceSpecialization,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let set_result = self.verify_objs_are_equal_in_equality_builtin(
            reduce.set.as_ref(),
            aggregate_set,
            line_file.clone(),
            builtin_state,
        )?;
        if !set_result.is_true() {
            return Ok(None);
        }
        let mut subgoals =
            equality_builtin_match_subgoals(reduce.set.as_ref(), aggregate_set, set_result);
        let function_result = self.verify_reduce_functions_pointwise_on_set(
            reduce.func.as_ref(),
            aggregate_func,
            reduce.set.as_ref(),
            line_file.clone(),
            builtin_state,
        )?;
        if !function_result.is_true() {
            return Ok(None);
        }
        subgoals.push(function_result);
        let identity = specialization.identity();
        let seed_result = self.verify_objs_are_equal_in_equality_builtin(
            reduce.seed.as_ref(),
            &identity,
            line_file.clone(),
            builtin_state,
        )?;
        if !seed_result.is_true() {
            return Ok(None);
        }
        subgoals.extend(equality_builtin_match_subgoals(
            reduce.seed.as_ref(),
            &identity,
            seed_result,
        ));
        let Some(carrier) = self.reduce_carrier_from_operation(reduce.op.as_ref()) else {
            return Ok(None);
        };
        let operation_result = self.verify_reduce_operation_matches_native(
            reduce.op.as_ref(),
            &carrier,
            specialization,
            line_file,
            builtin_state,
        )?;
        if !operation_result.is_true() {
            return Ok(None);
        }
        subgoals.push(operation_result);
        Ok(Some(subgoals))
    }

    fn verify_reduce_operation_matches_native(
        &mut self,
        operation: &Obj,
        carrier: &Obj,
        specialization: NativeReduceSpecialization,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let operation = operation.clone();
        let carrier = carrier.clone();
        self.run_in_local_env(|rt| {
            let x_name = rt.generate_random_unused_name();
            let y_name = rt.generate_random_unused_name();
            let (x_binding, x) = rt.fresh_bound_param(x_name, ParamObjType::Forall)?;
            let (y_binding, y) = rt.fresh_bound_param(y_name, ParamObjType::Forall)?;
            let params = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_binding, y_binding],
                ParamType::Obj(carrier),
            )]);
            rt.define_params_with_type(&params, false, ParamObjType::Forall)?;
            let Some(actual) =
                rt.instantiate_reduce_function_at(&operation, &[x.clone(), y.clone()])?
            else {
                return Ok(StmtUnknown::new().into());
            };
            let expected = specialization.apply(x, y);
            let equality: AtomicFact = EqualFact::new(actual, expected, line_file.clone()).into();
            let known_forall = rt.verify_atomic_fact_with_known_forall(
                &equality,
                &UseContextVerifyState::new(0, true),
            )?;
            if known_forall.is_true() {
                return Ok(known_forall);
            }
            rt.verify_builtin_rule_premise(&equality, builtin_state)
        })
    }

    fn verify_reduce_functions_pointwise_on_set(
        &mut self,
        left_func: &Obj,
        right_func: &Obj,
        set: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let direct = self.verify_objs_are_equal_in_equality_builtin(
            left_func,
            right_func,
            line_file.clone(),
            builtin_state,
        )?;
        if direct.is_true() {
            return Ok(direct);
        }
        for (first, second) in [
            (left_func.clone(), right_func.clone()),
            (right_func.clone(), left_func.clone()),
        ] {
            let fn_eq_in: AtomicFact =
                FnEqualInFact::new(first, second, set.clone(), line_file.clone()).into();
            let known = if let Some(result) =
                self.verify_fact_from_cache_using_display_string(&fn_eq_in.clone().into())
            {
                result
            } else {
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&fn_eq_in)?
            };
            if known.is_true() {
                return Ok(known);
            }
        }

        let left_func = left_func.clone();
        let right_func = right_func.clone();
        let set = set.clone();
        self.run_in_local_env(|rt| {
            let x_name = rt.generate_random_unused_name();
            let (x_binding, x) = rt.fresh_bound_param(x_name, ParamObjType::Forall)?;
            let params = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_binding],
                ParamType::Obj(set),
            )]);
            rt.define_params_with_type(&params, false, ParamObjType::Forall)?;
            let Some(left_value) = rt.instantiate_reduce_function_at(&left_func, &[x.clone()])?
            else {
                return Ok(StmtUnknown::new().into());
            };
            let Some(right_value) = rt.instantiate_reduce_function_at(&right_func, &[x])? else {
                return Ok(StmtUnknown::new().into());
            };
            let equality: AtomicFact =
                EqualFact::new(left_value, right_value, line_file.clone()).into();
            let known_forall = rt.verify_atomic_fact_with_known_forall(
                &equality,
                &UseContextVerifyState::new(0, true),
            )?;
            if known_forall.is_true() {
                return Ok(known_forall);
            }
            rt.verify_builtin_rule_premise(&equality, builtin_state)
        })
    }
}

#[derive(Clone, Copy)]
enum NativeReduceSpecialization {
    Additive,
    Multiplicative,
}

impl NativeReduceSpecialization {
    fn identity(self) -> Obj {
        match self {
            NativeReduceSpecialization::Additive => Number::new("0".to_string()).into(),
            NativeReduceSpecialization::Multiplicative => Number::new("1".to_string()).into(),
        }
    }

    fn apply(self, left: Obj, right: Obj) -> Obj {
        match self {
            NativeReduceSpecialization::Additive => Add::new(left, right).into(),
            NativeReduceSpecialization::Multiplicative => Mul::new(left, right).into(),
        }
    }
}
