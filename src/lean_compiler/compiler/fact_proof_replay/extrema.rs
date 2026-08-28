//! Minimum and maximum builtin evidence replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_extrema_from_result(
        &mut self,
        target: &Fact,
        rule: ExtremaBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let mut child_proofs = Vec::with_capacity(subgoals.len());
        let mut child_facts = Vec::with_capacity(subgoals.len());
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("extrema child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("extrema child {index} published effects"));
            }
            child_facts.push(child.fact());
            child_proofs.push(
                self.construct_lean_proof_from_direct_fact_result(child)?
                    .ok_or_else(|| format!("extrema child {index} has no direct proof consumer"))?,
            );
        }

        let render_reals = |objects: &[&Obj]| -> Result<Vec<String>, String> {
            objects
                .iter()
                .map(|object| {
                    render_real_target_object_representation(
                        &LeanTargetObjectRepresentation::lower(object)?,
                        &self.environment_stack,
                    )
                })
                .collect()
        };
        let same = |left: &Obj, right: &Obj| obj_equality_key(left) == obj_equality_key(right);
        let bridge_selected_source = |proof: String, selected: &Obj| -> Result<String, String> {
            let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                LeanTargetObjectRepresentation::lower(selected)?
            else {
                return Ok(proof);
            };
            let Some(source_to_selected) = self
                .environment_stack
                .numeric_representation_equalities
                .get(&symbol_id)
            else {
                return Ok(proof);
            };
            Ok(format!(
                "Litex.Same.trans ({proof}) (Litex.Same.symm ({source_to_selected}))"
            ))
        };
        let one_weak_premise = |expected_left: &Obj, expected_right: &Obj| -> Result<(), String> {
            let [premise] = child_facts.as_slice() else {
                return Err(format!(
                    "builtin rule `{}` requires one ordered premise",
                    rule.rule_id()
                ));
            };
            let (left, right, strict) = order_relation_parts(premise)?;
            if strict || !same(left, expected_left) || !same(right, expected_right) {
                return Err(format!(
                    "builtin rule `{}` changed its ordered premise",
                    rule.rule_id()
                ));
            }
            Ok(())
        };

        render_fact(target, &self.environment_stack)?;
        match rule {
            ExtremaBuiltinRule::MinLessEqualLeft
            | ExtremaBuiltinRule::MinLessEqualRight
            | ExtremaBuiltinRule::LessEqualMaxLeft
            | ExtremaBuiltinRule::LessEqualMaxRight => {
                if !subgoals.is_empty() {
                    return Err(format!(
                        "builtin rule `{}` unexpectedly gained child Results",
                        rule.rule_id()
                    ));
                }
                let (left, right, strict) = order_relation_parts(target)?;
                if strict {
                    return Err("extrema bound changed to strict order".into());
                }
                let (first, second, expected, theorem) = match rule {
                    ExtremaBuiltinRule::MinLessEqualLeft
                    | ExtremaBuiltinRule::MinLessEqualRight => {
                        let Obj::Min(minimum) = left else {
                            return Err("minimum bound lost its minimum constructor".into());
                        };
                        let (expected, theorem) = if rule == ExtremaBuiltinRule::MinLessEqualLeft {
                            (minimum.left.as_ref(), "minLeLeft")
                        } else {
                            (minimum.right.as_ref(), "minLeRight")
                        };
                        (
                            minimum.left.as_ref(),
                            minimum.right.as_ref(),
                            expected,
                            theorem,
                        )
                    }
                    ExtremaBuiltinRule::LessEqualMaxLeft
                    | ExtremaBuiltinRule::LessEqualMaxRight => {
                        let Obj::Max(maximum) = right else {
                            return Err("maximum bound lost its maximum constructor".into());
                        };
                        let (expected, theorem) = if rule == ExtremaBuiltinRule::LessEqualMaxLeft {
                            (maximum.left.as_ref(), "leMaxLeft")
                        } else {
                            (maximum.right.as_ref(), "leMaxRight")
                        };
                        (
                            maximum.left.as_ref(),
                            maximum.right.as_ref(),
                            expected,
                            theorem,
                        )
                    }
                    _ => unreachable!(),
                };
                let actual = if matches!(
                    rule,
                    ExtremaBuiltinRule::MinLessEqualLeft | ExtremaBuiltinRule::MinLessEqualRight
                ) {
                    right
                } else {
                    left
                };
                if !same(actual, expected) {
                    return Err("extrema bound changed its selected operand".into());
                }
                let arguments = render_reals(&[first, second])?;
                Ok(Some(format!(
                    "Litex.Rules.{theorem} {} {}",
                    arguments[0], arguments[1]
                )))
            }
            ExtremaBuiltinRule::MinEqLeftOfLessEqual
            | ExtremaBuiltinRule::MinEqRightOfLessEqual
            | ExtremaBuiltinRule::MaxEqLeftOfLessEqual
            | ExtremaBuiltinRule::MaxEqRightOfLessEqual => {
                let (equality_left, equality_right) = equality_parts(target)?;
                let mut selected = None;
                for (operator, result, reverse) in [
                    (equality_left, equality_right, false),
                    (equality_right, equality_left, true),
                ] {
                    let (first, second) = match operator {
                        Obj::Min(value)
                            if matches!(
                                rule,
                                ExtremaBuiltinRule::MinEqLeftOfLessEqual
                                    | ExtremaBuiltinRule::MinEqRightOfLessEqual
                            ) =>
                        {
                            (value.left.as_ref(), value.right.as_ref())
                        }
                        Obj::Max(value)
                            if matches!(
                                rule,
                                ExtremaBuiltinRule::MaxEqLeftOfLessEqual
                                    | ExtremaBuiltinRule::MaxEqRightOfLessEqual
                            ) =>
                        {
                            (value.left.as_ref(), value.right.as_ref())
                        }
                        _ => continue,
                    };
                    let (expected_result, premise_left, premise_right, theorem) = match rule {
                        ExtremaBuiltinRule::MinEqLeftOfLessEqual => {
                            (first, first, second, "minEqLeftOfLe")
                        }
                        ExtremaBuiltinRule::MinEqRightOfLessEqual => {
                            (second, second, first, "minEqRightOfLe")
                        }
                        ExtremaBuiltinRule::MaxEqLeftOfLessEqual => {
                            (first, second, first, "maxEqLeftOfLe")
                        }
                        ExtremaBuiltinRule::MaxEqRightOfLessEqual => {
                            (second, first, second, "maxEqRightOfLe")
                        }
                        _ => unreachable!(),
                    };
                    if same(result, expected_result) {
                        selected = Some((
                            first,
                            second,
                            expected_result,
                            premise_left,
                            premise_right,
                            theorem,
                            reverse,
                        ));
                        break;
                    }
                }
                let Some((
                    first,
                    second,
                    selected_result,
                    premise_left,
                    premise_right,
                    theorem,
                    reverse,
                )) = selected
                else {
                    return Err("extrema selection equality changed its structure".into());
                };
                one_weak_premise(premise_left, premise_right)?;
                let arguments = render_reals(&[first, second])?;
                let proof = format!(
                    "Litex.Rules.{theorem} {} {} ({})",
                    arguments[0], arguments[1], child_proofs[0]
                );
                let mut proof = bridge_selected_source(proof, selected_result)?;
                if reverse {
                    proof = format!("Litex.Same.symm ({proof})");
                }
                Ok(Some(proof))
            }
            ExtremaBuiltinRule::MinMonotone | ExtremaBuiltinRule::MaxMonotone => {
                let [first_premise, second_premise] = child_facts.as_slice() else {
                    return Err("extrema monotonicity requires two ordered premises".into());
                };
                let (left, right, strict) = order_relation_parts(target)?;
                if strict {
                    return Err("extrema monotonicity changed to strict order".into());
                }
                let (first, second, third, fourth, theorem) = match (rule, left, right) {
                    (ExtremaBuiltinRule::MinMonotone, Obj::Min(left), Obj::Min(right)) => (
                        left.left.as_ref(),
                        left.right.as_ref(),
                        right.left.as_ref(),
                        right.right.as_ref(),
                        "minMonotone",
                    ),
                    (ExtremaBuiltinRule::MaxMonotone, Obj::Max(left), Obj::Max(right)) => (
                        left.left.as_ref(),
                        left.right.as_ref(),
                        right.left.as_ref(),
                        right.right.as_ref(),
                        "maxMonotone",
                    ),
                    _ => return Err("extrema monotonicity changed its constructors".into()),
                };
                for (premise, expected_left, expected_right) in [
                    (first_premise, first, third),
                    (second_premise, second, fourth),
                ] {
                    let (premise_left, premise_right, premise_strict) =
                        order_relation_parts(premise)?;
                    if premise_strict
                        || !same(premise_left, expected_left)
                        || !same(premise_right, expected_right)
                    {
                        return Err("extrema monotonicity changed its ordered premises".into());
                    }
                }
                let arguments = render_reals(&[first, second, third, fourth])?;
                Ok(Some(format!(
                    "Litex.Rules.{theorem} {} {} {} {} ({}) ({})",
                    arguments[0],
                    arguments[1],
                    arguments[2],
                    arguments[3],
                    child_proofs[0],
                    child_proofs[1]
                )))
            }
            ExtremaBuiltinRule::MinCommutative
            | ExtremaBuiltinRule::MinAssociative
            | ExtremaBuiltinRule::MinIdempotent
            | ExtremaBuiltinRule::MinAbsorbMaxLeft
            | ExtremaBuiltinRule::MaxCommutative
            | ExtremaBuiltinRule::MaxAssociative
            | ExtremaBuiltinRule::MaxIdempotent
            | ExtremaBuiltinRule::MaxAbsorbMinLeft => {
                if !subgoals.is_empty() {
                    return Err("extrema lattice identity unexpectedly gained child Results".into());
                }
                let (left, right) = equality_parts(target)?;
                let mut matched = None;
                for (source, destination, reverse) in [(left, right, false), (right, left, true)] {
                    let candidate = match rule {
                        ExtremaBuiltinRule::MinCommutative => match (source, destination) {
                            (Obj::Min(source), Obj::Min(destination))
                                if same(source.left.as_ref(), destination.right.as_ref())
                                    && same(source.right.as_ref(), destination.left.as_ref()) =>
                            {
                                Some((
                                    vec![source.left.as_ref(), source.right.as_ref()],
                                    "minCommutative",
                                ))
                            }
                            _ => None,
                        },
                        ExtremaBuiltinRule::MaxCommutative => match (source, destination) {
                            (Obj::Max(source), Obj::Max(destination))
                                if same(source.left.as_ref(), destination.right.as_ref())
                                    && same(source.right.as_ref(), destination.left.as_ref()) =>
                            {
                                Some((
                                    vec![source.left.as_ref(), source.right.as_ref()],
                                    "maxCommutative",
                                ))
                            }
                            _ => None,
                        },
                        ExtremaBuiltinRule::MinIdempotent => match source {
                            Obj::Min(value)
                                if same(value.left.as_ref(), value.right.as_ref())
                                    && same(value.left.as_ref(), destination) =>
                            {
                                Some((vec![value.left.as_ref()], "minIdempotent"))
                            }
                            _ => None,
                        },
                        ExtremaBuiltinRule::MaxIdempotent => match source {
                            Obj::Max(value)
                                if same(value.left.as_ref(), value.right.as_ref())
                                    && same(value.left.as_ref(), destination) =>
                            {
                                Some((vec![value.left.as_ref()], "maxIdempotent"))
                            }
                            _ => None,
                        },
                        ExtremaBuiltinRule::MinAbsorbMaxLeft => match source {
                            Obj::Min(value) if same(value.left.as_ref(), destination) => {
                                match value.right.as_ref() {
                                    Obj::Max(inner) if same(inner.left.as_ref(), destination) => {
                                        Some((
                                            vec![destination, inner.right.as_ref()],
                                            "minAbsorbMaxLeft",
                                        ))
                                    }
                                    _ => None,
                                }
                            }
                            _ => None,
                        },
                        ExtremaBuiltinRule::MaxAbsorbMinLeft => match source {
                            Obj::Max(value) if same(value.left.as_ref(), destination) => {
                                match value.right.as_ref() {
                                    Obj::Min(inner) if same(inner.left.as_ref(), destination) => {
                                        Some((
                                            vec![destination, inner.right.as_ref()],
                                            "maxAbsorbMinLeft",
                                        ))
                                    }
                                    _ => None,
                                }
                            }
                            _ => None,
                        },
                        ExtremaBuiltinRule::MinAssociative => match (source, destination) {
                            (Obj::Min(source), Obj::Min(destination)) => {
                                match (source.left.as_ref(), destination.right.as_ref()) {
                                    (Obj::Min(inner_left), Obj::Min(inner_right))
                                        if same(
                                            inner_left.left.as_ref(),
                                            destination.left.as_ref(),
                                        ) && same(
                                            inner_left.right.as_ref(),
                                            inner_right.left.as_ref(),
                                        ) && same(
                                            source.right.as_ref(),
                                            inner_right.right.as_ref(),
                                        ) =>
                                    {
                                        Some((
                                            vec![
                                                inner_left.left.as_ref(),
                                                inner_left.right.as_ref(),
                                                source.right.as_ref(),
                                            ],
                                            "minAssociative",
                                        ))
                                    }
                                    _ => None,
                                }
                            }
                            _ => None,
                        },
                        ExtremaBuiltinRule::MaxAssociative => match (source, destination) {
                            (Obj::Max(source), Obj::Max(destination)) => {
                                match (source.left.as_ref(), destination.right.as_ref()) {
                                    (Obj::Max(inner_left), Obj::Max(inner_right))
                                        if same(
                                            inner_left.left.as_ref(),
                                            destination.left.as_ref(),
                                        ) && same(
                                            inner_left.right.as_ref(),
                                            inner_right.left.as_ref(),
                                        ) && same(
                                            source.right.as_ref(),
                                            inner_right.right.as_ref(),
                                        ) =>
                                    {
                                        Some((
                                            vec![
                                                inner_left.left.as_ref(),
                                                inner_left.right.as_ref(),
                                                source.right.as_ref(),
                                            ],
                                            "maxAssociative",
                                        ))
                                    }
                                    _ => None,
                                }
                            }
                            _ => None,
                        },
                        _ => unreachable!(),
                    };
                    if let Some((arguments, theorem)) = candidate {
                        matched = Some((arguments, theorem, destination, reverse));
                        break;
                    }
                }
                let Some((arguments, theorem, selected_result, reverse)) = matched else {
                    return Err(format!(
                        "builtin rule `{}` changed its lattice identity",
                        rule.rule_id()
                    ));
                };
                let rendered = render_reals(&arguments)?;
                let proof = format!("Litex.Rules.{theorem} {}", rendered.join(" "));
                let mut proof = bridge_selected_source(proof, selected_result)?;
                if reverse {
                    proof = format!("Litex.Same.symm ({proof})");
                }
                Ok(Some(proof))
            }
        }
    }
}
