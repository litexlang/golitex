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
}
