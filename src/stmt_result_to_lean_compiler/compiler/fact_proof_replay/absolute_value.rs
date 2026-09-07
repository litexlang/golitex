//! Absolute-value builtin evidence replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Replay the legacy typed absolute-value evidence. Sign selection is
    /// accepted only when its ordered child is rendered against the exact
    /// native real selected for the target symbol; semantic `Same` is never
    /// eliminated into native equality.
    pub(in super::super) fn construct_lean_absolute_value_from_result(
        &mut self,
        target: &Fact,
        rule: AbsoluteValueBuiltinRule,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if rule == AbsoluteValueBuiltinRule::UpperBound {
            let (target_left, bound, target_strict) = order_relation_parts(target)?;
            let Obj::Abs(absolute) = target_left else {
                return Err("absolute-value upper bound lost its absolute-value target".into());
            };
            let argument = absolute.arg.as_ref();
            let [upper, lower] = subgoals else {
                return Err(
                    "absolute-value upper bound requires two retained order premises".into(),
                );
            };
            let mut compile_child = |child: &VerifyFactResult, role: &str| {
                let child = child
                    .verified()
                    .ok_or_else(|| format!("absolute-value {role} premise is not factual"))?;
                let proof = self
                    .construct_lean_proof_from_direct_fact_result(child)?
                    .ok_or_else(|| {
                        format!("absolute-value {role} premise has no direct proof consumer")
                    })?;
                Ok::<_, String>((child.fact(), proof))
            };
            let (upper_fact, upper_proof) = compile_child(upper, "upper")?;
            let (lower_fact, lower_proof) = compile_child(lower, "lower")?;
            let (upper_left, upper_right, upper_strict) = order_relation_parts(&upper_fact)?;
            if obj_equality_key(upper_left) != obj_equality_key(argument)
                || obj_equality_key(upper_right) != obj_equality_key(bound)
                || upper_strict != target_strict
            {
                return Err(
                    "absolute-value upper premise changed its endpoints or strictness".into(),
                );
            }
            let (lower_left, lower_right, lower_strict) = order_relation_parts(&lower_fact)?;
            if lower_strict != target_strict {
                return Err("absolute-value lower premise changed relation strictness".into());
            }
            let negated_argument = |candidate: &Obj, expected: &Obj| {
                let Obj::Mul(product) = candidate else {
                    return false;
                };
                let is_negative_one = |object: &Obj| matches!(object, Obj::Number(number) if number.normalized_value == "-1");
                (is_negative_one(product.left.as_ref())
                    && obj_equality_key(product.right.as_ref()) == obj_equality_key(expected))
                    || (is_negative_one(product.right.as_ref())
                        && obj_equality_key(product.left.as_ref()) == obj_equality_key(expected))
            };
            let lower_is_neg_bound = negated_argument(lower_left, bound)
                && obj_equality_key(lower_right) == obj_equality_key(argument);
            let lower_is_neg_argument = negated_argument(lower_left, argument)
                && obj_equality_key(lower_right) == obj_equality_key(bound);
            if !lower_is_neg_bound && !lower_is_neg_argument {
                return Err("absolute-value lower premise changed its sandwich endpoints".into());
            }
            let argument_real = render_real_target_object_representation(
                &LeanTargetObjectRepresentation::lower(argument)?,
                &self.environment_stack,
            )?;
            let bound_real = render_real_target_object_representation(
                &LeanTargetObjectRepresentation::lower(bound)?,
                &self.environment_stack,
            )?;
            render_fact(target, &self.environment_stack)?;
            let relation = if target_strict {
                "Litex.Lt"
            } else {
                "Litex.Le"
            };
            let theorem = match (target_strict, lower_is_neg_bound) {
                (false, true) => "Litex.Rules.realCastAbsLeOfUpperAndLower",
                (false, false) => "Litex.Rules.realCastAbsLeOfUpperAndNegUpper",
                (true, true) => "Litex.Rules.realCastAbsLtOfUpperAndLower",
                (true, false) => "Litex.Rules.realCastAbsLtOfUpperAndNegUpper",
            };
            let lower_native_left = if lower_is_neg_bound {
                format!("(-({bound_real}) : ℝ)")
            } else {
                format!("(-({argument_real}) : ℝ)")
            };
            let lower_native_right = if lower_is_neg_bound {
                argument_real.clone()
            } else {
                bound_real.clone()
            };
            let simp = "Litex.fnApply, Litex.fnApplyOwn, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_div";
            return Ok(Some(format!(
                "(by\n  have __abs_upper : {relation} (({argument_real} : ℝ) : ℂ) (({bound_real} : ℝ) : ℂ) := by\n    convert ({upper_proof}) using 1 <;> simp [{simp}] <;> norm_num <;> norm_cast\n  have __abs_lower : {relation} (({lower_native_left} : ℝ) : ℂ) (({lower_native_right} : ℝ) : ℂ) := by\n    convert ({lower_proof}) using 1 <;> simp [{simp}] <;> norm_num <;> norm_cast\n  convert ({theorem} (a := {argument_real}) (b := {bound_real}) __abs_upper __abs_lower) using 1 <;> simp [{simp}] <;> norm_num <;> norm_cast)"
            )));
        }
        if matches!(
            rule,
            AbsoluteValueBuiltinRule::Nonnegative
                | AbsoluteValueBuiltinRule::SelfLessEqual
                | AbsoluteValueBuiltinRule::NegationLessEqual
                | AbsoluteValueBuiltinRule::NegativeAbsoluteLessEqual
                | AbsoluteValueBuiltinRule::TriangleAdd
                | AbsoluteValueBuiltinRule::TriangleSub
                | AbsoluteValueBuiltinRule::ReverseTriangleAdd
                | AbsoluteValueBuiltinRule::ReverseTriangleSub
        ) {
            if !subgoals.is_empty() {
                return Err(format!(
                    "builtin rule `{}` unexpectedly gained child Results",
                    rule.rule_id()
                ));
            }
            let (left, right, strict) = order_relation_parts(target)?;
            if strict {
                return Err(format!(
                    "builtin rule `{}` changed to strict order",
                    rule.rule_id()
                ));
            }
            let is_negation_of = |candidate: &Obj, argument: &Obj| {
                let Obj::Mul(product) = candidate else {
                    return false;
                };
                let is_negative_one = |object: &Obj| matches!(object, Obj::Number(number) if number.normalized_value == "-1");
                (is_negative_one(product.left.as_ref())
                    && obj_equality_key(product.right.as_ref()) == obj_equality_key(argument))
                    || (is_negative_one(product.right.as_ref())
                        && obj_equality_key(product.left.as_ref()) == obj_equality_key(argument))
            };
            fn abs_argument(object: &Obj) -> Option<&Obj> {
                match object {
                    Obj::Abs(absolute) => Some(absolute.arg.as_ref()),
                    _ => None,
                }
            }
            fn abs_pair(object: &Obj) -> Option<(&Obj, &Obj)> {
                let Obj::Add(sum) = object else {
                    return None;
                };
                Some((
                    abs_argument(sum.left.as_ref())?,
                    abs_argument(sum.right.as_ref())?,
                ))
            }
            let (arguments, theorem): (Vec<&Obj>, &str) = match rule {
                AbsoluteValueBuiltinRule::Nonnegative => {
                    let argument = abs_argument(right)
                        .filter(|_| is_literal_zero(left))
                        .ok_or_else(|| {
                            "absolute-value nonnegative target changed shape".to_string()
                        })?;
                    (vec![argument], "absNonnegative")
                }
                AbsoluteValueBuiltinRule::SelfLessEqual => {
                    let argument = abs_argument(right)
                        .filter(|argument| obj_equality_key(left) == obj_equality_key(argument))
                        .ok_or_else(|| "self-to-absolute bound changed shape".to_string())?;
                    (vec![argument], "selfLeAbs")
                }
                AbsoluteValueBuiltinRule::NegationLessEqual => {
                    let argument = abs_argument(right)
                        .filter(|argument| is_negation_of(left, argument))
                        .ok_or_else(|| "negated-to-absolute bound changed shape".to_string())?;
                    (vec![argument], "negLeAbs")
                }
                AbsoluteValueBuiltinRule::NegativeAbsoluteLessEqual => {
                    let Obj::Mul(product) = left else {
                        return Err("negative-absolute lower bound lost its negation".into());
                    };
                    let absolute = if matches!(product.left.as_ref(), Obj::Number(number) if number.normalized_value == "-1")
                    {
                        product.right.as_ref()
                    } else if matches!(product.right.as_ref(), Obj::Number(number) if number.normalized_value == "-1")
                    {
                        product.left.as_ref()
                    } else {
                        return Err("negative-absolute lower bound lost negative one".into());
                    };
                    let argument = abs_argument(absolute)
                        .filter(|argument| obj_equality_key(right) == obj_equality_key(argument))
                        .ok_or_else(|| {
                            "negative-absolute lower bound changed its argument".to_string()
                        })?;
                    (vec![argument], "negAbsLe")
                }
                AbsoluteValueBuiltinRule::TriangleAdd | AbsoluteValueBuiltinRule::TriangleSub => {
                    let outer = abs_argument(left).ok_or_else(|| {
                        "absolute triangle target lost its outer absolute value".to_string()
                    })?;
                    let (first, second) = match (rule, outer) {
                        (AbsoluteValueBuiltinRule::TriangleAdd, Obj::Add(sum)) => {
                            (sum.left.as_ref(), sum.right.as_ref())
                        }
                        (AbsoluteValueBuiltinRule::TriangleSub, Obj::Sub(difference)) => {
                            (difference.left.as_ref(), difference.right.as_ref())
                        }
                        _ => return Err("absolute triangle target changed its operator".into()),
                    };
                    let (right_first, right_second) = abs_pair(right).ok_or_else(|| {
                        "absolute triangle target lost its absolute-value sum".to_string()
                    })?;
                    if !((obj_equality_key(first) == obj_equality_key(right_first)
                        && obj_equality_key(second) == obj_equality_key(right_second))
                        || (obj_equality_key(first) == obj_equality_key(right_second)
                            && obj_equality_key(second) == obj_equality_key(right_first)))
                    {
                        return Err("absolute triangle target changed its operands".into());
                    }
                    (
                        vec![first, second],
                        if rule == AbsoluteValueBuiltinRule::TriangleAdd {
                            "absAddLe"
                        } else {
                            "absSubLeSum"
                        },
                    )
                }
                AbsoluteValueBuiltinRule::ReverseTriangleAdd
                | AbsoluteValueBuiltinRule::ReverseTriangleSub => {
                    let Obj::Sub(difference) = left else {
                        return Err("reverse absolute triangle lost its difference".into());
                    };
                    let first = abs_argument(difference.left.as_ref()).ok_or_else(|| {
                        "reverse absolute triangle lost its left absolute value".to_string()
                    })?;
                    let second = abs_argument(difference.right.as_ref()).ok_or_else(|| {
                        "reverse absolute triangle lost its right absolute value".to_string()
                    })?;
                    let outer = abs_argument(right).ok_or_else(|| {
                        "reverse absolute triangle lost its outer absolute value".to_string()
                    })?;
                    let operands_match = match (rule, outer) {
                        (AbsoluteValueBuiltinRule::ReverseTriangleAdd, Obj::Add(sum)) => {
                            (obj_equality_key(first) == obj_equality_key(sum.left.as_ref())
                                && obj_equality_key(second) == obj_equality_key(sum.right.as_ref()))
                                || (obj_equality_key(first) == obj_equality_key(sum.right.as_ref())
                                    && obj_equality_key(second)
                                        == obj_equality_key(sum.left.as_ref()))
                        }
                        (AbsoluteValueBuiltinRule::ReverseTriangleSub, Obj::Sub(subtraction)) => {
                            obj_equality_key(first) == obj_equality_key(subtraction.left.as_ref())
                                && obj_equality_key(second)
                                    == obj_equality_key(subtraction.right.as_ref())
                        }
                        _ => false,
                    };
                    if !operands_match {
                        return Err("reverse absolute triangle changed its operands".into());
                    }
                    (
                        vec![first, second],
                        if rule == AbsoluteValueBuiltinRule::ReverseTriangleAdd {
                            "absSubAbsLeAbsAdd"
                        } else {
                            "absSubAbsLeAbsSub"
                        },
                    )
                }
                _ => unreachable!("matched zero-premise absolute-value rule"),
            };
            render_fact(target, &self.environment_stack)?;
            let rendered_arguments = arguments
                .into_iter()
                .map(|argument| render_numeric_obj(argument, &self.environment_stack))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(Some(format!(
                "Litex.Rules.{theorem} {}",
                rendered_arguments.join(" ")
            )));
        }
        if rule != AbsoluteValueBuiltinRule::Product {
            let [child] = subgoals else {
                return Err("absolute-value sign evidence requires one retained premise".into());
            };
            let child = child
                .verified()
                .ok_or_else(|| "absolute-value sign premise is not factual".to_string())?;
            let child_fact = child.fact();
            let child_proof = self
                .construct_lean_proof_from_direct_fact_result(child)?
                .ok_or_else(|| {
                    "absolute-value sign premise has no direct proof consumer".to_string()
                })?;
            render_fact(target, &self.environment_stack)?;

            return match rule {
                AbsoluteValueBuiltinRule::NonnegativeIdentity
                | AbsoluteValueBuiltinRule::NonpositiveNegation => {
                    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
                        return Err(
                            "absolute-value sign-selection evidence targets a non-equality fact"
                                .into(),
                        );
                    };
                    fn selection<'a>(
                        absolute_side: &'a Obj,
                        selected_side: &Obj,
                        rule: AbsoluteValueBuiltinRule,
                    ) -> Option<&'a Obj> {
                        let Obj::Abs(absolute) = absolute_side else {
                            return None;
                        };
                        let argument = absolute.arg.as_ref();
                        match rule {
                            AbsoluteValueBuiltinRule::NonnegativeIdentity
                                if obj_equality_key(argument)
                                    == obj_equality_key(selected_side) =>
                            {
                                Some(argument)
                            }
                            AbsoluteValueBuiltinRule::NonpositiveNegation => {
                                let Obj::Mul(product) = selected_side else {
                                    return None;
                                };
                                let is_negative_one = |object: &Obj| matches!(object, Obj::Number(number) if number.normalized_value == "-1");
                                let matches = (is_negative_one(product.left.as_ref())
                                    && obj_equality_key(product.right.as_ref())
                                        == obj_equality_key(argument))
                                    || (is_negative_one(product.right.as_ref())
                                        && obj_equality_key(product.left.as_ref())
                                            == obj_equality_key(argument));
                                matches.then_some(argument)
                            }
                            _ => None,
                        }
                    }
                    let (argument, reversed) = if let Some(argument) =
                        selection(&equality.left, &equality.right, rule)
                    {
                        (argument, false)
                    } else if let Some(argument) = selection(&equality.right, &equality.left, rule)
                    {
                        (argument, true)
                    } else {
                        return Err(
                            "absolute-value sign-selection evidence changed its structural target"
                                .into(),
                        );
                    };
                    let (premise_left, premise_right, strict) = order_relation_parts(&child_fact)?;
                    let premise_matches = match rule {
                        AbsoluteValueBuiltinRule::NonnegativeIdentity => {
                            is_literal_zero(premise_left)
                                && obj_equality_key(premise_right) == obj_equality_key(argument)
                        }
                        AbsoluteValueBuiltinRule::NonpositiveNegation => {
                            obj_equality_key(premise_left) == obj_equality_key(argument)
                                && is_literal_zero(premise_right)
                        }
                        _ => false,
                    };
                    if !premise_matches {
                        return Err(
                            "absolute-value sign-selection evidence changed its ordered premise"
                                .into(),
                        );
                    }
                    let native_real = render_real_target_object_representation(
                        &LeanTargetObjectRepresentation::lower(argument)?,
                        &self.environment_stack,
                    )?;
                    let weak_premise = if strict {
                        format!(
                            "(by simpa [Litex.Le, Litex.Lt, Litex.OrderValue] using (le_of_lt (show _ < _ from {child_proof})))"
                        )
                    } else {
                        format!("({child_proof})")
                    };
                    let theorem = match rule {
                        AbsoluteValueBuiltinRule::NonnegativeIdentity => "absEqSelfOfLe",
                        AbsoluteValueBuiltinRule::NonpositiveNegation => "absEqNegOfLe",
                        _ => unreachable!(),
                    };
                    let mut proof = format!("Litex.Rules.{theorem} {native_real} {weak_premise}");
                    if rule == AbsoluteValueBuiltinRule::NonnegativeIdentity {
                        if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                            LeanTargetObjectRepresentation::lower(argument)?
                        {
                            if let Some(binding) = self
                                .environment_stack
                                .exact_carrier_source_equalities
                                .get(&symbol_id)
                            {
                                let real = self
                                    .environment_stack
                                    .numeric_real_values
                                    .get(&symbol_id)
                                    .cloned()
                                    .ok_or_else(|| {
                                        "absolute-value exact carrier has no retained real value"
                                            .to_string()
                                    })?;
                                // `In.same_rep` deliberately uses the
                                // default observer for a heterogeneous
                                // source.  Here the source is already the
                                // exact `R.Carrier`, so close the final
                                // homogeneous endpoint with proof-irrelevant
                                // `In.rep_exact` and let `Same.ofEq` infer the
                                // real observer.
                                let _ = binding;
                                proof = format!(
                                    "Litex.Same.trans ({proof}) (Litex.Same.trans (Litex.Same.symm (Litex.Same.realComplex ({real}))) (Litex.Same.ofEq (by simp [Litex.In.rep])))"
                                );
                            } else if let Some(source_to_selected) = self
                                .environment_stack
                                .numeric_representation_equalities
                                .get(&symbol_id)
                            {
                                let source_bridge = if self
                                    .environment_stack
                                    .exact_carrier_values
                                    .contains_key(&symbol_id)
                                {
                                    format!(
                                        "Litex.Same.trans (Litex.Same.symm ({source_to_selected})) (Litex.Same.ofEq (by simp [Litex.In.rep]))"
                                    )
                                } else {
                                    format!("Litex.Same.symm ({source_to_selected})")
                                };
                                proof = format!("Litex.Same.trans ({proof}) ({source_bridge})");
                            }
                        }
                    }
                    if reversed {
                        proof = format!("Litex.Same.symm ({proof})");
                    }
                    Ok(Some(proof))
                }
                AbsoluteValueBuiltinRule::PositiveFromNonzero => {
                    let (zero, absolute_value) = positive_order_parts(target, true)?;
                    if !is_literal_zero(zero) {
                        return Err(
                            "absolute-value positivity target changed its zero endpoint".into()
                        );
                    }
                    let Obj::Abs(absolute_value) = absolute_value else {
                        return Err("absolute-value positivity target lost its abs operator".into());
                    };
                    let argument = absolute_value.arg.as_ref();
                    let (nonzero_left, nonzero_right) = not_equal_parts(&child_fact)?;
                    if obj_equality_key(nonzero_left) != obj_equality_key(argument)
                        || !is_literal_zero(nonzero_right)
                    {
                        return Err(
                            "absolute-value positivity evidence changed its nonzero premise".into(),
                        );
                    }
                    let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                        LeanTargetObjectRepresentation::lower(argument)?
                    else {
                        return Err(
                            "absolute-value positivity requires one exact source symbol".into()
                        );
                    };
                    let source = render_obj(argument, &self.environment_stack)?;
                    let native_real = render_real_target_object_representation(
                        &LeanTargetObjectRepresentation::lower(argument)?,
                        &self.environment_stack,
                    )?;
                    let (theorem, source_to_selected) = if let Some(binding) = self
                        .environment_stack
                        .exact_carrier_source_equalities
                        .get(&symbol_id)
                    {
                        let membership = cached_exact_membership_selection_proof(
                            &binding.exact_value,
                            &source,
                        )
                        .ok_or_else(|| {
                            "absolute-value positivity exact carrier lost its membership proof"
                                .to_string()
                        })?;
                        let source_is_native_real =
                            native_real == source || native_real == format!("({source} : ℝ)");
                        let source_to_selected = if source_is_native_real {
                            format!("Litex.Same.realComplexNoObservation ({native_real})")
                        } else {
                            format!(
                                "Litex.Same.transNoObservation (Litex.Same.symmNoObservation (Litex.Same.withoutObservation (Litex.In.same_rep {source} ({membership})))) (Litex.Same.realComplexNoObservation ({native_real}))"
                            )
                        };
                        ("absPositiveOfNotSameNoObservation", source_to_selected)
                    } else {
                        // `R` forall binders intentionally keep their source
                        // value on the complex host ABI, so they do not
                        // populate the numeric-equality cache used by native
                        // integer/rational consumers. Their visible
                        // membership proof still selects the exact real
                        // representative needed by abs positivity. Reuse
                        // that Result-owned proof directly and keep the
                        // bridge observation-free; this does not infer a
                        // native equality for the source binder.
                        let membership = resolve_visible_exact_membership_proof(
                            argument,
                            &Obj::StandardSet(StandardSet::R),
                            &self.environment_stack,
                        )
                        .map_err(|_| {
                            "absolute-value positivity has no source-to-real representation bridge"
                                .to_string()
                        })?;
                        let source_to_selected = format!(
                            "Litex.Same.transNoObservation (Litex.Same.withoutObservation (Litex.In.same_rep {source} ({membership}))) (Litex.Same.realComplexNoObservation ({native_real}))"
                        );
                        ("absPositiveOfNotSameNoObservation", source_to_selected)
                    };
                    Ok(Some(format!(
                        "Litex.Rules.{theorem} {source} {native_real} ({source_to_selected}) ({child_proof})"
                    )))
                }
                AbsoluteValueBuiltinRule::UpperBound => {
                    unreachable!("absolute-value upper-bound rule returned above")
                }
                AbsoluteValueBuiltinRule::Product => unreachable!(),
                AbsoluteValueBuiltinRule::Nonnegative
                | AbsoluteValueBuiltinRule::SelfLessEqual
                | AbsoluteValueBuiltinRule::NegationLessEqual
                | AbsoluteValueBuiltinRule::NegativeAbsoluteLessEqual
                | AbsoluteValueBuiltinRule::TriangleAdd
                | AbsoluteValueBuiltinRule::TriangleSub
                | AbsoluteValueBuiltinRule::ReverseTriangleAdd
                | AbsoluteValueBuiltinRule::ReverseTriangleSub => {
                    unreachable!("zero-premise absolute-value rule returned above")
                }
            };
        }
        if !subgoals.is_empty() {
            return Err("absolute-value product gained unexpected proof children".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
            return Err("absolute-value product evidence targets a non-equality fact".into());
        };
        let product_shape = |abs_side: &Obj, product_side: &Obj| -> Option<(Obj, Obj)> {
            let Obj::Abs(abs) = abs_side else {
                return None;
            };
            let Obj::Mul(arguments) = abs.arg.as_ref() else {
                return None;
            };
            let Obj::Mul(values) = product_side else {
                return None;
            };
            let (Obj::Abs(left_abs), Obj::Abs(right_abs)) =
                (values.left.as_ref(), values.right.as_ref())
            else {
                return None;
            };
            if obj_equality_key(arguments.left.as_ref()) != obj_equality_key(left_abs.arg.as_ref())
                || obj_equality_key(arguments.right.as_ref())
                    != obj_equality_key(right_abs.arg.as_ref())
            {
                return None;
            }
            Some((
                arguments.left.as_ref().clone(),
                arguments.right.as_ref().clone(),
            ))
        };
        let (left, right, reversed) =
            if let Some((left, right)) = product_shape(&equality.left, &equality.right) {
                (left, right, false)
            } else if let Some((left, right)) = product_shape(&equality.right, &equality.left) {
                (left, right, true)
            } else {
                return Err("absolute-value product evidence changed its structural target".into());
            };
        let proof = format!(
            "Litex.Rules.absMul {} {}",
            render_numeric_obj(&left, &self.environment_stack)?,
            render_numeric_obj(&right, &self.environment_stack)?
        );
        Ok(Some(if reversed {
            format!("Litex.Same.symm ({proof})")
        } else {
            proof
        }))
    }
}
