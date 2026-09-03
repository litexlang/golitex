use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

impl Runtime {
    pub fn verify_abs_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(f) = &norm else {
            return Ok(None);
        };
        if let Some(result) = self.try_verify_abs_basic_lower_bound(f, atomic_fact)? {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_abs_finite_sum_triangle(f, atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_abs_finite_set_sum_triangle(f, atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_triangle(f, atomic_fact)? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_reverse_triangle(f, atomic_fact)? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_upper_bound(
            &f.left,
            &f.right,
            &f.line_file,
            atomic_fact,
            false,
            builtin_state,
        )? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_lower_bound_from_abs_compare(
            &f.left,
            &f.right,
            &f.line_file,
            atomic_fact,
            false,
            builtin_state,
        )? {
            return Ok(Some(result));
        }
        Ok(None)
    }

    pub fn verify_abs_order_strict_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(f) = &norm else {
            return Ok(None);
        };
        if let Some(result) =
            self.try_verify_abs_positive_from_arg_nonzero(f, atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_upper_bound(
            &f.left,
            &f.right,
            &f.line_file,
            atomic_fact,
            true,
            builtin_state,
        )? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_lower_bound_from_abs_compare(
            &f.left,
            &f.right,
            &f.line_file,
            atomic_fact,
            true,
            builtin_state,
        )? {
            return Ok(Some(result));
        }
        Ok(None)
    }
}

fn literal_neg_one_obj() -> Obj {
    Obj::Number(Number::new("-1".to_string()))
}

fn literal_zero_obj() -> Obj {
    Obj::Number(Number::new("0".to_string()))
}

fn obj_is_literal_zero(obj: &Obj) -> bool {
    match obj {
        Obj::Number(n) => n.normalized_value == "0",
        _ => false,
    }
}

fn obj_is_literal_neg_one(obj: &Obj) -> bool {
    match obj {
        Obj::Number(n) => n.normalized_value == "-1",
        _ => false,
    }
}

fn neg_obj(obj: &Obj) -> Obj {
    Mul::new(literal_neg_one_obj(), obj.clone()).into()
}

fn objs_have_same_display(a: &Obj, b: &Obj) -> bool {
    a.to_string() == b.to_string()
}

fn obj_is_negation_of(obj: &Obj, expected_arg: &Obj) -> bool {
    match obj {
        Obj::Mul(m) => {
            (obj_is_literal_neg_one(m.left.as_ref())
                && objs_have_same_display(m.right.as_ref(), expected_arg))
                || (obj_is_literal_neg_one(m.right.as_ref())
                    && objs_have_same_display(m.left.as_ref(), expected_arg))
        }
        _ => false,
    }
}

fn obj_is_abs_of(obj: &Obj, arg: &Obj) -> bool {
    match obj {
        Obj::Abs(abs) => objs_have_same_display(abs.arg.as_ref(), arg),
        _ => false,
    }
}

fn obj_is_add_of_abs_pair(obj: &Obj, x: &Obj, y: &Obj) -> bool {
    let Obj::Add(add) = obj else {
        return false;
    };
    (obj_is_abs_of(add.left.as_ref(), x) && obj_is_abs_of(add.right.as_ref(), y))
        || (obj_is_abs_of(add.left.as_ref(), y) && obj_is_abs_of(add.right.as_ref(), x))
}

fn obj_is_abs_of_add_pair(obj: &Obj, x: &Obj, y: &Obj) -> bool {
    let Obj::Abs(abs) = obj else {
        return false;
    };
    let Obj::Add(add) = abs.arg.as_ref() else {
        return false;
    };
    (objs_have_same_display(add.left.as_ref(), x) && objs_have_same_display(add.right.as_ref(), y))
        || (objs_have_same_display(add.left.as_ref(), y)
            && objs_have_same_display(add.right.as_ref(), x))
}

fn obj_is_abs_of_sub_pair(obj: &Obj, x: &Obj, y: &Obj) -> bool {
    let Obj::Abs(abs) = obj else {
        return false;
    };
    let Obj::Sub(sub) = abs.arg.as_ref() else {
        return false;
    };
    objs_have_same_display(sub.left.as_ref(), x) && objs_have_same_display(sub.right.as_ref(), y)
}

fn abs_obj(arg: Obj) -> Obj {
    Abs::new(arg).into()
}

fn abs_order_subgoal(left: Obj, right: Obj, line_file: LineFile, strict: bool) -> AtomicFact {
    if strict {
        LessFact::new(left, right, line_file).into()
    } else {
        LessEqualFact::new(left, right, line_file).into()
    }
}

fn peel_negation(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::Mul(m) => {
            if obj_is_literal_neg_one(m.left.as_ref()) {
                Some(m.right.as_ref())
            } else if obj_is_literal_neg_one(m.right.as_ref()) {
                Some(m.left.as_ref())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn peel_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::Abs(abs) => Some(abs.arg.as_ref()),
        _ => None,
    }
}

impl Runtime {
    fn verify_abs_order_subgoal(
        &mut self,
        fact: AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<VerifyFactResult>, RuntimeError> {
        self.try_verify_atomic_fact_as_builtin_rule_premise(&fact, builtin_state)
    }

    // Absolute value bounds: -abs(x) <= x <= abs(x), and -x <= abs(x).
    // Example: `forall x R: x <= abs(x)`.
    fn try_verify_abs_basic_lower_bound(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if let Obj::Abs(abs) = &f.right {
            let rule = if objs_have_same_display(&f.left, abs.arg.as_ref()) {
                Some(AbsoluteValueBuiltinRule::SelfLessEqual)
            } else if obj_is_negation_of(&f.left, abs.arg.as_ref()) {
                Some(AbsoluteValueBuiltinRule::NegationLessEqual)
            } else {
                None
            };
            if let Some(rule) = rule {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "abs: x <= abs(x) and -x <= abs(x)".to_string(),
                        BuiltinRuleEvidence::AbsoluteValue(rule),
                        Vec::new(),
                    ),
                )));
            }
        }

        let abs_right: Obj = Abs::new(f.right.clone()).into();
        if !obj_is_negation_of(&f.left, &abs_right) {
            return Ok(None);
        }
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "abs: -abs(x) <= x".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(
                    AbsoluteValueBuiltinRule::NegativeAbsoluteLessEqual,
                ),
                Vec::new(),
            ),
        )))
    }

    // Finite sum triangle inequality.
    // Example: `abs(sum(m, n, fn(i Z) R {a(i)})) <= sum(m, n, fn(i Z) R {abs(a(i))})`.
    fn try_verify_abs_finite_sum_triangle(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::Abs(abs) = &f.left else {
            return Ok(None);
        };
        let Obj::Sum(left_sum) = abs.arg.as_ref() else {
            return Ok(None);
        };
        let Obj::Sum(right_sum) = &f.right else {
            return Ok(None);
        };

        let start_fact: AtomicFact = EqualFact::new(
            left_sum.start.as_ref().clone(),
            right_sum.start.as_ref().clone(),
            f.line_file.clone(),
        )
        .into();
        let Some(start_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&start_fact, builtin_state)?
        else {
            return Ok(None);
        };
        let end_fact: AtomicFact = EqualFact::new(
            left_sum.end.as_ref().clone(),
            right_sum.end.as_ref().clone(),
            f.line_file.clone(),
        )
        .into();
        let Some(end_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&end_fact, builtin_state)?
        else {
            return Ok(None);
        };

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
        let Some(left_inst) =
            self.instantiate_unary_anonymous_summand_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_anonymous_summand_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let pointwise_fact: AtomicFact =
            EqualFact::new(right_inst, abs_obj(left_inst), f.line_file.clone()).into();
        let dom_lo: Fact = LessEqualFact::new(
            (*left_sum.start).clone(),
            x_obj.clone(),
            f.line_file.clone(),
        )
        .into();
        let dom_hi: Fact =
            LessEqualFact::new(x_obj, (*left_sum.end).clone(), f.line_file.clone()).into();
        let pointwise_result = self.run_in_local_verification_env(
            builtin_state.verify_state(),
            |rt, local_verify_state| {
                let local_builtin_state = builtin_state.with_verify_state(local_verify_state);
                let params_def = TypedParameterList::new(vec![TypedParameterGroup::new(
                    vec![x_binding],
                    ParamType::Obj(StandardSet::Z.into()),
                )]);
                rt.define_params_with_type(&params_def, false, BindingScope::LocalBinder)?;
                rt.store_fact_without_forall_coverage_check_and_infer(dom_lo)?;
                rt.store_fact_without_forall_coverage_check_and_infer(dom_hi)?;
                rt.try_verify_atomic_fact_as_builtin_rule_premise(
                    &pointwise_fact,
                    &local_builtin_state,
                )
            },
        )?;
        let Some(pointwise_result) = pointwise_result else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "abs: finite sum triangle inequality".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyAbsFiniteSumTriangle,
                ),
                vec![start_result, end_result, pointwise_result],
            ),
        )))
    }

    // Finite-set sum triangle inequality.
    // Example: `abs(finite_set_sum(X, f)) <= finite_set_sum(X, fn(x X) R {abs(f(x))})`.
    fn try_verify_abs_finite_set_sum_triangle(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::Abs(abs) = &f.left else {
            return Ok(None);
        };
        let Obj::SumOfFiniteSet(left_sum) = abs.arg.as_ref() else {
            return Ok(None);
        };
        let Obj::SumOfFiniteSet(right_sum) = &f.right else {
            return Ok(None);
        };

        let set_fact: AtomicFact = EqualFact::new(
            left_sum.set.as_ref().clone(),
            right_sum.set.as_ref().clone(),
            f.line_file.clone(),
        )
        .into();
        let Some(set_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&set_fact, builtin_state)?
        else {
            return Ok(None);
        };

        let x_name = self.generate_random_unused_name();
        let (x_binding, x_obj) = self.fresh_bound_param(x_name)?;
        let Some(left_inst) = self.instantiate_unary_function_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_function_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let pointwise_fact: AtomicFact =
            EqualFact::new(right_inst, abs_obj(left_inst), f.line_file.clone()).into();
        let pointwise_result = self.run_in_local_verification_env(
            builtin_state.verify_state(),
            |rt, local_verify_state| {
                let local_builtin_state = builtin_state.with_verify_state(local_verify_state);
                let params_def = TypedParameterList::new(vec![TypedParameterGroup::new(
                    vec![x_binding],
                    ParamType::Obj(left_sum.set.as_ref().clone()),
                )]);
                rt.define_params_with_type(&params_def, false, BindingScope::LocalBinder)?;
                rt.try_verify_atomic_fact_as_builtin_rule_premise(
                    &pointwise_fact,
                    &local_builtin_state,
                )
            },
        )?;
        let Some(pointwise_result) = pointwise_result else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "abs: finite-set sum triangle inequality".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyAbsFiniteSetSumTriangle,
                ),
                vec![set_result, pointwise_result],
            ),
        )))
    }

    // Absolute values of nonzero real expressions are strictly positive.
    // Example: `forall x R: x != 0 => abs(x) > 0`.
    fn try_verify_abs_positive_from_arg_nonzero(
        &mut self,
        f: &LessFact,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if !obj_is_literal_zero(&f.left) {
            return Ok(None);
        }
        let Obj::Abs(abs) = &f.right else {
            return Ok(None);
        };
        let arg_nonzero: AtomicFact = NotEqualFact::new(
            abs.arg.as_ref().clone(),
            literal_zero_obj(),
            f.line_file.clone(),
        )
        .into();
        let Some(nonzero_result) = self.verify_abs_order_subgoal(arg_nonzero, builtin_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "abs: 0 < abs(x) from x != 0".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(AbsoluteValueBuiltinRule::PositiveFromNonzero),
                vec![nonzero_result],
            ),
        )))
    }

    // Absolute value upper bound: abs(x) <= b from x <= b and -x <= b.
    // Strict form: abs(x) < b from x < b and -x < b.
    // Example: `forall x, b R: x <= b, -x <= b => abs(x) <= b`.
    fn try_verify_abs_upper_bound(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: &LineFile,
        atomic_fact: &AtomicFact,
        strict: bool,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::Abs(abs) = left else {
            return Ok(None);
        };
        let arg = abs.arg.as_ref();
        let arg_le_bound = abs_order_subgoal(arg.clone(), right.clone(), line_file.clone(), strict);
        let neg_arg_le_bound =
            abs_order_subgoal(neg_obj(arg), right.clone(), line_file.clone(), strict);
        let neg_bound_le_arg =
            abs_order_subgoal(neg_obj(right), arg.clone(), line_file.clone(), strict);
        let Some(r1) = self.verify_abs_order_subgoal(arg_le_bound, builtin_state)? else {
            return Ok(None);
        };
        // Accept either common spelling of the lower side of the sandwich:
        // `-x < b` or, equivalently, `-b < x`. Checking the latter directly
        // avoids requiring a second order-algebra builtin hop.
        let direct_lower = self.verify_abs_order_subgoal(neg_bound_le_arg, builtin_state)?;
        let r2 = match direct_lower {
            Some(direct_lower) => Some(direct_lower),
            None => self.verify_abs_order_subgoal(neg_arg_le_bound, builtin_state)?,
        };
        let Some(r2) = r2 else {
            return Ok(None);
        };
        let rule = if strict {
            "abs: abs(x) < b from -b < x < b"
        } else {
            "abs: abs(x) <= b from -b <= x <= b"
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                rule.to_string(),
                BuiltinRuleEvidence::AbsoluteValue(AbsoluteValueBuiltinRule::UpperBound),
                vec![r1, r2],
            ),
        )))
    }

    // Converse of abs upper bound: sandwich bounds from abs(x) <= abs(y) (or strict <).
    // Examples:
    // `forall x, y R: abs(x) <= abs(y) => -abs(y) <= x <= abs(y)`
    // `forall x, y R: abs(x) <= abs(y), 0 <= y => -y <= x <= y`
    // `forall x, y R: abs(x) <= abs(y), y <= 0 => y <= x <= -y`
    fn try_verify_abs_lower_bound_from_abs_compare(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: &LineFile,
        atomic_fact: &AtomicFact,
        strict: bool,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let rule_suffix = if strict { " (strict)" } else { "" };
        let zero: Obj = Number::new("0".to_string()).into();

        // -abs(y) <= x from abs(x) <= abs(y); or -y <= x when 0 <= y.
        if let Some(inner) = peel_negation(left) {
            if let Some(y) = peel_abs(inner) {
                if let Some(r) = self.verify_known_abs_compare(
                    right,
                    &abs_obj(y.clone()),
                    line_file,
                    strict,
                    builtin_state.verify_state(),
                )? {
                    let rule = format!(
                        "abs: -abs(y) {} x from abs(x) {} abs(y){}",
                        if strict { "<" } else { "<=" },
                        if strict { "<" } else { "<=" },
                        rule_suffix
                    );
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            rule,
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAbsLowerBoundFromAbsCompare01),
                            vec![r],
                        ),
                    )));
                }
            } else {
                let y = inner;
                if let Some(r) = self.verify_known_abs_compare(
                    right,
                    &abs_obj(y.clone()),
                    line_file,
                    strict,
                    builtin_state.verify_state(),
                )? {
                    let ge_y: AtomicFact =
                        GreaterEqualFact::new(y.clone(), zero.clone(), line_file.clone()).into();
                    if let Some(r_sign) = self.verify_abs_order_subgoal(ge_y, builtin_state)? {
                        let rule = format!(
                            "abs: -y {} x from abs(x) {} abs(y) and 0 <= y{}",
                            if strict { "<" } else { "<=" },
                            if strict { "<" } else { "<=" },
                            rule_suffix
                        );
                        return Ok(Some(ProveFactResult::from(
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                atomic_fact.clone().into(),
                                rule,
                                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAbsLowerBoundFromAbsCompare02),
                                vec![r, r_sign],
                            ),
                        )));
                    }
                }
            }
        }

        // x <= bound or x < bound from abs(x) <= bound (or strict).
        if let Some(r) = self.verify_known_abs_compare(
            left,
            right,
            line_file,
            strict,
            builtin_state.verify_state(),
        )? {
            let rule = format!(
                "abs: x {} b from abs(x) {} b{}",
                if strict { "<" } else { "<=" },
                if strict { "<" } else { "<=" },
                rule_suffix
            );
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    rule,
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyAbsLowerBoundFromAbsCompare03,
                    ),
                    vec![r],
                ),
            )));
        }

        // -x <= bound or -x < bound from abs(x) <= bound (or strict).
        if let Some(arg) = peel_negation(left) {
            if let Some(r) = self.verify_known_abs_compare(
                arg,
                right,
                line_file,
                strict,
                builtin_state.verify_state(),
            )? {
                let rule = format!(
                    "abs: -x {} b from abs(x) {} b{}",
                    if strict { "<" } else { "<=" },
                    if strict { "<" } else { "<=" },
                    rule_suffix
                );
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        rule,
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAbsLowerBoundFromAbsCompare04),
                        vec![r],
                    ),
                )));
            }
        }

        // y <= x from abs(x) <= abs(y) and y <= 0.
        if let Some(r) = self.verify_known_abs_compare(
            right,
            &abs_obj(left.clone()),
            line_file,
            strict,
            builtin_state.verify_state(),
        )? {
            let le_y: AtomicFact =
                LessEqualFact::new(left.clone(), zero.clone(), line_file.clone()).into();
            let r_sign = if strict {
                self.try_verify_atomic_fact_as_builtin_rule_premise(&le_y, builtin_state)?
            } else {
                self.verify_abs_order_subgoal(le_y, builtin_state)?
            };
            if let Some(r_sign) = r_sign {
                let rule = format!(
                    "abs: y {} x from abs(x) {} abs(y) and y <= 0{}",
                    if strict { "<" } else { "<=" },
                    if strict { "<" } else { "<=" },
                    rule_suffix
                );
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        rule,
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAbsLowerBoundFromAbsCompare05),
                        vec![r, r_sign],
                    ),
                )));
            }
        }

        // x <= -y from abs(x) <= abs(y) and y <= 0.
        if let Some(y) = peel_negation(right) {
            if let Some(r) = self.verify_known_abs_compare(
                left,
                &abs_obj(y.clone()),
                line_file,
                strict,
                builtin_state.verify_state(),
            )? {
                let le_y: AtomicFact =
                    LessEqualFact::new(y.clone(), zero.clone(), line_file.clone()).into();
                let r_sign = if strict {
                    self.try_verify_atomic_fact_as_builtin_rule_premise(&le_y, builtin_state)?
                } else {
                    self.verify_abs_order_subgoal(le_y, builtin_state)?
                };
                if let Some(r_sign) = r_sign {
                    let rule = format!(
                        "abs: x {} -y from abs(x) {} abs(y) and y <= 0{}",
                        if strict { "<" } else { "<=" },
                        if strict { "<" } else { "<=" },
                        rule_suffix
                    );
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            rule,
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAbsLowerBoundFromAbsCompare06),
                            vec![r, r_sign],
                        ),
                    )));
                }
            }
        }

        // x <= y from abs(x) <= abs(y) and 0 <= y.
        if let Some(r) = self.verify_known_abs_compare(
            left,
            &abs_obj(right.clone()),
            line_file,
            strict,
            builtin_state.verify_state(),
        )? {
            let ge_y: AtomicFact =
                GreaterEqualFact::new(right.clone(), zero.clone(), line_file.clone()).into();
            if let Some(r_sign) = self.verify_abs_order_subgoal(ge_y, builtin_state)? {
                let rule = format!(
                    "abs: x {} y from abs(x) {} abs(y) and 0 <= y{}",
                    if strict { "<" } else { "<=" },
                    if strict { "<" } else { "<=" },
                    rule_suffix
                );
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        rule,
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::TryVerifyAbsLowerBoundFromAbsCompare07),
                        vec![r, r_sign],
                    ),
                )));
            }
        }

        Ok(None)
    }

    fn verify_known_abs_compare(
        &mut self,
        arg: &Obj,
        bound: &Obj,
        line_file: &LineFile,
        strict: bool,
        verify_state: &VerifyState,
    ) -> Result<Option<VerifyFactResult>, RuntimeError> {
        let fact = abs_order_subgoal(
            abs_obj(arg.clone()),
            bound.clone(),
            line_file.clone(),
            strict,
        );
        let target: Fact = fact.clone().into();
        if let Some(proof) = self.verification_result_from_known_fact_cache(&target) {
            let checked = self.verify_fact_well_defined_result(&target, verify_state)?;
            return Ok(Some(Runtime::finish_fact_verification(checked, proof)));
        }
        Ok(None)
    }

    // Triangle inequality for addition and subtraction.
    // Examples: `abs(x + y) <= abs(x) + abs(y)`, `abs(x - y) <= abs(x) + abs(y)`.
    fn try_verify_abs_triangle(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::Abs(abs) = &f.left else {
            return Ok(None);
        };
        let rule = match abs.arg.as_ref() {
            Obj::Add(add) => {
                obj_is_add_of_abs_pair(&f.right, add.left.as_ref(), add.right.as_ref())
                    .then_some(AbsoluteValueBuiltinRule::TriangleAdd)
            }
            Obj::Sub(sub) => {
                obj_is_add_of_abs_pair(&f.right, sub.left.as_ref(), sub.right.as_ref())
                    .then_some(AbsoluteValueBuiltinRule::TriangleSub)
            }
            _ => None,
        };
        let Some(rule) = rule else {
            return Ok(None);
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "abs: triangle inequality".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(rule),
                Vec::new(),
            ),
        )))
    }

    // Weak reverse triangle inequality.
    // Examples: `abs(x) - abs(y) <= abs(x + y)`, `abs(x) - abs(y) <= abs(x - y)`.
    fn try_verify_abs_reverse_triangle(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::Sub(sub) = &f.left else {
            return Ok(None);
        };
        let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (sub.left.as_ref(), sub.right.as_ref())
        else {
            return Ok(None);
        };
        let x = left_abs.arg.as_ref();
        let y = right_abs.arg.as_ref();
        let rule = if obj_is_abs_of_add_pair(&f.right, x, y) {
            Some(AbsoluteValueBuiltinRule::ReverseTriangleAdd)
        } else if obj_is_abs_of_sub_pair(&f.right, x, y) {
            Some(AbsoluteValueBuiltinRule::ReverseTriangleSub)
        } else {
            None
        };
        let Some(rule) = rule else {
            return Ok(None);
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "abs: weak reverse triangle inequality".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(rule),
                Vec::new(),
            ),
        )))
    }
}
