//! Aggregate builtin evidence replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_aggregate_from_result(
        &mut self,
        target: &Fact,
        rule: AggregateBuiltinRule,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        let (equality_left, equality_right) = equality_parts(target)?;
        let same = |left: &Obj, right: &Obj| obj_equality_key(left) == obj_equality_key(right);
        let application_matches = |object: &Obj, function: &Obj, argument: &Obj| {
            let Obj::FnObj(application) = object else {
                return false;
            };
            let head: Obj = application.head.as_ref().clone().into();
            same(&head, function)
                && matches!(application.body.as_slice(), [layer] if matches!(layer.as_slice(), [retained] if same(retained.as_ref(), argument)))
        };
        let add_one_matches = |object: &Obj, base: &Obj| {
            let Obj::Add(addition) = object else {
                return false;
            };
            same(addition.left.as_ref(), base)
                && matches!(addition.right.as_ref(), Obj::Number(number) if number.normalized_value == "1")
        };
        let equality_matches_unordered = |fact: &Fact, first: &Obj, second: &Obj| {
            let Ok((left, right)) = equality_parts(fact) else {
                return false;
            };
            (same(left, first) && same(right, second)) || (same(left, second) && same(right, first))
        };

        match rule {
            AggregateBuiltinRule::SumSingle => {
                let [singleton_range_child, value_child] = subgoals else {
                    return Err(
                        "aggregate.sum_single requires its range and summand equality Results"
                            .into(),
                    );
                };
                let singleton_range_child = singleton_range_child
                    .verified()
                    .ok_or_else(|| "aggregate.sum_single range child is not factual".to_string())?;
                let value_child = value_child.verified().ok_or_else(|| {
                    "aggregate.sum_single summand child is not factual".to_string()
                })?;
                let mut matched = None;
                for (sum_side, application_side, reverse) in [
                    (equality_left, equality_right, false),
                    (equality_right, equality_left, true),
                ] {
                    let Obj::Sum(sum) = sum_side else {
                        continue;
                    };
                    if same(sum.start.as_ref(), sum.end.as_ref()) {
                        matched = Some((sum, application_side, reverse));
                        break;
                    }
                }
                let Some((sum, application, reverse)) = matched else {
                    return Err(format!(
                        "aggregate.sum_single changed its target structure: retained target `{target}`"
                    ));
                };
                if !equality_matches_unordered(
                    &singleton_range_child.fact(),
                    sum.start.as_ref(),
                    sum.end.as_ref(),
                ) {
                    return Err("aggregate.sum_single changed one of its retained premises".into());
                }
                let value_fact = value_child.fact();
                let (value_left, value_right) = equality_parts(&value_fact)?;
                let value_child_reversed = if same(value_right, application) {
                    false
                } else if same(value_left, application) {
                    true
                } else {
                    return Err(
                        "aggregate.sum_single value child no longer proves the retained target"
                            .into(),
                    );
                };
                self.construct_lean_proof_from_direct_fact_result(singleton_range_child)?
                    .ok_or_else(|| {
                        "aggregate.sum_single range child has no direct proof consumer".to_string()
                    })?;
                let mut value_proof = self
                    .construct_lean_proof_from_direct_fact_result(value_child)?
                    .ok_or_else(|| {
                        "aggregate.sum_single summand child has no direct proof consumer"
                            .to_string()
                    })?;
                if value_child_reversed {
                    value_proof = format!("Litex.Same.symm ({value_proof})");
                }
                render_fact(target, &self.environment_stack)?;
                let start = render_integer_obj(sum.start.as_ref(), &self.environment_stack)?;
                let lowered_function = LeanTargetObjectRepresentation::lower(sum.func.as_ref())?;
                let (exact_function, heterogeneous) = render_exact_unary_integer_function(
                    &lowered_function,
                    &self.environment_stack,
                )?;
                let base_proof = match heterogeneous {
                    None => {
                        format!("Litex.Rules.integerRangeSumSingleOwn {start} {exact_function}")
                    }
                    Some((source, membership)) => {
                        format!("Litex.Rules.integerRangeSumSingle {start} {source} ({membership})")
                    }
                };
                let mut proof = format!("Litex.Same.trans ({base_proof}) ({value_proof})");
                if reverse {
                    proof = format!("Litex.Same.symm ({proof})");
                }
                Ok(Some(proof))
            }
            AggregateBuiltinRule::SumSplitLast => {
                let [start_child, end_child, function_child, tail_child, order_child] = subgoals
                else {
                    return Err(
                        "aggregate.sum_split_last requires its four equality Results and ordered-range Result"
                            .into(),
                    );
                };
                let verified_children =
                    [start_child, end_child, function_child, tail_child].map(|child| {
                        child.verified().ok_or_else(|| {
                            "aggregate.sum_split_last equality child is not factual".to_string()
                        })
                    });
                let [start_child, end_child, function_child, tail_child] = verified_children
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()?
                    .try_into()
                    .expect("four checked equality children");
                let order_child = order_child.verified().ok_or_else(|| {
                    "aggregate.sum_split_last ordered child is not factual".to_string()
                })?;
                let order_fact = order_child.fact();
                let order_proof = self
                    .construct_lean_proof_from_direct_fact_result(order_child)?
                    .ok_or_else(|| {
                        "aggregate.sum_split_last child has no direct proof consumer".to_string()
                    })?;
                let mut matched = None;
                for (extended_side, decomposition_side, reverse) in [
                    (equality_left, equality_right, false),
                    (equality_right, equality_left, true),
                ] {
                    let (Obj::Sum(extended), Obj::Add(decomposition)) =
                        (extended_side, decomposition_side)
                    else {
                        continue;
                    };
                    let Obj::Sum(previous) = decomposition.left.as_ref() else {
                        continue;
                    };
                    if !same(extended.start.as_ref(), previous.start.as_ref())
                        || !add_one_matches(extended.end.as_ref(), previous.end.as_ref())
                        || !same(extended.func.as_ref(), previous.func.as_ref())
                        || !application_matches(
                            decomposition.right.as_ref(),
                            extended.func.as_ref(),
                            extended.end.as_ref(),
                        )
                    {
                        continue;
                    }
                    let (premise_left, premise_right, premise_strict) =
                        order_relation_parts(&order_fact)?;
                    if premise_strict
                        || !same(premise_left, previous.start.as_ref())
                        || !same(premise_right, previous.end.as_ref())
                    {
                        continue;
                    }
                    matched = Some((extended, previous, decomposition.right.as_ref(), reverse));
                    break;
                }
                let Some((extended, previous, tail, reverse)) = matched else {
                    return Err("aggregate.sum_split_last changed its target or premise".into());
                };
                let previous_end_plus_one: Obj = Add::new(
                    previous.end.as_ref().clone(),
                    Number::new("1".into()).into(),
                )
                .into();
                if !equality_matches_unordered(
                    &start_child.fact(),
                    extended.start.as_ref(),
                    previous.start.as_ref(),
                ) || !equality_matches_unordered(
                    &end_child.fact(),
                    extended.end.as_ref(),
                    &previous_end_plus_one,
                ) || !equality_matches_unordered(
                    &function_child.fact(),
                    extended.func.as_ref(),
                    previous.func.as_ref(),
                ) || !equality_matches_unordered(&tail_child.fact(), tail, tail)
                {
                    return Err(
                        "aggregate.sum_split_last changed one of its retained equality premises"
                            .into(),
                    );
                }
                for child in [start_child, end_child, function_child, tail_child] {
                    self.construct_lean_proof_from_direct_fact_result(child)?
                        .ok_or_else(|| {
                            "aggregate.sum_split_last equality child has no direct proof consumer"
                                .to_string()
                        })?;
                }
                render_fact(target, &self.environment_stack)?;
                let start = render_integer_obj(extended.start.as_ref(), &self.environment_stack)?;
                let finish = render_integer_obj(previous.end.as_ref(), &self.environment_stack)?;
                let lowered_function =
                    LeanTargetObjectRepresentation::lower(extended.func.as_ref())?;
                let (exact_function, heterogeneous) = render_exact_unary_integer_function(
                    &lowered_function,
                    &self.environment_stack,
                )?;
                let native_order =
                    format!("(by simpa [Litex.Le, Litex.OrderValue] using ({order_proof}))");
                let mut proof = match heterogeneous {
                    None => format!(
                        "Litex.Rules.integerRangeSumSplitLastOwn {start} {finish} {exact_function} ({native_order})"
                    ),
                    Some((source, membership)) => format!(
                        "Litex.Rules.integerRangeSumSplitLast {start} {finish} {source} ({membership}) ({native_order})"
                    ),
                };
                if reverse {
                    proof = format!("Litex.Same.symm ({proof})");
                }
                Ok(Some(proof))
            }
        }
    }
}
