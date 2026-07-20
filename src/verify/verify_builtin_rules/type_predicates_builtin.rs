use crate::prelude::*;

impl Runtime {
    pub fn _verify_is_nonempty_set_fact_with_builtin_rules(
        &mut self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Empty set rule: `$is_nonempty_set(S)` follows from `S != {}`.
        // Example: after `S != {}`, prove `$is_nonempty_set(S)`.
        let empty_set: Obj = ListSet::new(vec![]).into();
        let not_equal_empty: AtomicFact = NotEqualFact::new(
            is_nonempty_set_fact.set.clone(),
            empty_set,
            is_nonempty_set_fact.line_file.clone(),
        )
        .into();
        let not_equal_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&not_equal_empty)?;
        if not_equal_result.is_true() {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    is_nonempty_set_fact.clone().into(),
                    InferResult::new(),
                    "nonempty_set_from_not_equal_empty_set".to_string(),
                    vec![not_equal_result],
                )
                .into(),
            );
        }

        if let Some(result) = self.try_verify_nonempty_finite_set_from_positive_finite_set_size(
            is_nonempty_set_fact,
            _verify_state,
        )? {
            return Ok(result);
        }

        match &is_nonempty_set_fact.set {
            Obj::StandardSet(_) => Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    is_nonempty_set_fact.clone().into(),
                    "standard_nonempty_set".to_string(),
                    Vec::new(),
                ))
                .into(),
            ),
            Obj::ListSet(list_set) => {
                if list_set.list.is_empty() {
                    Ok((StmtUnknown::new()).into())
                } else {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "list_set_nonempty_has_member_in_syntax".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                }
            }
            // Power set nonempty rule: `power_set(S)` contains the empty set as a subset of `S`.
            // Example: prove `$is_nonempty_set(power_set(Z))`.
            Obj::PowerSet(_) => Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    is_nonempty_set_fact.clone().into(),
                    "power_set_is_nonempty_because_empty_set_is_subset".to_string(),
                    Vec::new(),
                ))
                .into(),
            ),
            // Integer closed interval `{x in Z | lo <= x <= hi}` is nonempty iff `lo <= hi`.
            // The interval itself is total, so nonemptiness still needs a provable `lo <= hi`.
            // Example: `$is_nonempty_set(closed_range(0, 2))` via `0 <= 2`.
            // Example: under `a <= b`, the same for `closed_range(a, b)`.
            Obj::ClosedRange(closed_range) => {
                let le = LessEqualFact::new(
                    closed_range.start.as_ref().clone(),
                    closed_range.end.as_ref().clone(),
                    is_nonempty_set_fact.line_file.clone(),
                );
                let le_ok = self.verify_non_equational_known_then_builtin_rules_only(
                    &le.into(),
                    _verify_state,
                )?;
                if le_ok.is_true() {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "closed_range_nonempty_when_start_le_end".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            // Real interval nonempty rules depend on the endpoint openness.
            // Closed/closed is nonempty from `a <= b`; the other three require `a < b`.
            // Example: `$is_nonempty_set('[a, b])` from `a <= b`.
            // Example: `$is_nonempty_set('(a, b))` from `a < b`.
            Obj::IntervalObj(interval) => {
                let order_fact: AtomicFact = if interval.left_closed() && interval.right_closed() {
                    LessEqualFact::new(
                        interval.start().clone(),
                        interval.end().clone(),
                        is_nonempty_set_fact.line_file.clone(),
                    )
                    .into()
                } else {
                    LessFact::new(
                        interval.start().clone(),
                        interval.end().clone(),
                        is_nonempty_set_fact.line_file.clone(),
                    )
                    .into()
                };
                let order_ok = self.verify_non_equational_known_then_builtin_rules_only(
                    &order_fact,
                    _verify_state,
                )?;
                if order_ok.is_true() {
                    let rule = match interval {
                        IntervalObj::LeftOpenRightOpen(_) => {
                            "open_interval_nonempty_when_start_lt_end"
                        }
                        IntervalObj::LeftOpenRightClosed(_) => {
                            "left_open_right_closed_interval_nonempty_when_start_lt_end"
                        }
                        IntervalObj::LeftClosedRightOpen(_) => {
                            "left_closed_right_open_interval_nonempty_when_start_lt_end"
                        }
                        IntervalObj::LeftClosedRightClosed(_) => {
                            "closed_interval_nonempty_when_start_le_end"
                        }
                    };
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            rule.to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            // Half-infinite real intervals are nonempty whenever their finite endpoint is well-defined.
            // Example: `$is_nonempty_set('[a,))` after `a $in R`.
            Obj::OneSideInfinityIntervalObj(interval) => {
                let rule = match interval {
                    OneSideInfinityIntervalObj::LeftOpen(_) => {
                        "right_unbounded_open_interval_nonempty_with_real_endpoint"
                    }
                    OneSideInfinityIntervalObj::LeftClosed(_) => {
                        "right_unbounded_closed_interval_nonempty_with_real_endpoint"
                    }
                    OneSideInfinityIntervalObj::RightOpen(_) => {
                        "left_unbounded_open_interval_nonempty_with_real_endpoint"
                    }
                    OneSideInfinityIntervalObj::RightClosed(_) => {
                        "left_unbounded_closed_interval_nonempty_with_real_endpoint"
                    }
                };
                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_nonempty_set_fact.clone().into(),
                        rule.to_string(),
                        Vec::new(),
                    ))
                    .into(),
                )
            }
            // A union is nonempty when either side is nonempty.
            // Example: from `$is_nonempty_set(A)`, prove `$is_nonempty_set(union(A, B))`.
            Obj::Union(union) => {
                let left_nonempty: AtomicFact = IsNonemptySetFact::new(
                    union.left.as_ref().clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let left_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &left_nonempty,
                    _verify_state,
                )?;
                if left_result.is_true() {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "union_is_nonempty_set_when_left_side_is_nonempty_set".to_string(),
                            vec![left_result],
                        ))
                        .into(),
                    );
                }

                let right_nonempty: AtomicFact = IsNonemptySetFact::new(
                    union.right.as_ref().clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let right_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &right_nonempty,
                    _verify_state,
                )?;
                if right_result.is_true() {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "union_is_nonempty_set_when_right_side_is_nonempty_set".to_string(),
                            vec![right_result],
                        ))
                        .into(),
                    );
                }

                Ok((StmtUnknown::new()).into())
            }
            Obj::Cart(cart) => {
                for arg_obj in &cart.args {
                    let is_nonempty_set_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &IsNonemptySetFact::new(
                                *arg_obj.clone(),
                                is_nonempty_set_fact.line_file.clone(),
                            )
                            .into(),
                            _verify_state,
                        )?;

                    if is_nonempty_set_result.is_unknown() {
                        return Ok((StmtUnknown::new()).into());
                    }
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_nonempty_set_fact.clone().into(),
                        format!(
                            "sets `{}` in `{}` are nonempty sets",
                            cart.args
                                .iter()
                                .map(|arg| arg.as_ref().to_string())
                                .collect::<Vec<String>>()
                                .join(", "),
                            cart.to_string()
                        ),
                        Vec::new(),
                    ))
                    .into(),
                )
            }
            Obj::FnSet(fn_set) => {
                let ret_nonempty_fact = IsNonemptySetFact::new(
                    fn_set.body.ret_set.as_ref().clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let ret_check = self.verify_non_equational_known_then_builtin_rules_only(
                    &ret_nonempty_fact,
                    _verify_state,
                )?;
                if ret_check.is_true() {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "fn_set_is_nonempty_when_ret_set_is_nonempty".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            Obj::AnonymousFn(anon) => {
                let ret_nonempty_fact = IsNonemptySetFact::new(
                    anon.body.ret_set.as_ref().clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let ret_check = self.verify_non_equational_known_then_builtin_rules_only(
                    &ret_nonempty_fact,
                    _verify_state,
                )?;
                if ret_check.is_true() {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "fn_set_is_nonempty_when_ret_set_is_nonempty".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            // Axiom of choice for an indexed family: if every factor selected by `g`
            // is nonempty, then `general_cart(I, s, g)` is nonempty.
            // Example: from `forall X s: $is_nonempty_set(X)`, prove
            // `$is_nonempty_set(general_cart(I, s, g))`.
            // Also accepts the pointwise form `forall alpha I: $is_nonempty_set(g(alpha))`.
            Obj::GeneralCart(general_cart) => {
                let global_fact =
                    general_cart_global_family_nonempty_fact(general_cart, is_nonempty_set_fact);
                let global_result = self.verify_fact_full(&global_fact, _verify_state)?;
                if global_result.is_true() {
                    return Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "axiom_of_choice: general_cart is nonempty when every set in the family set is nonempty"
                                .to_string(),
                            vec![global_result],
                        )
                        .into(),
                    );
                }

                let Some(pointwise_fact) = general_cart_pointwise_family_nonempty_fact(
                    general_cart,
                    is_nonempty_set_fact,
                )?
                else {
                    return Ok((StmtUnknown::new()).into());
                };
                let pointwise_result = self.verify_fact_full(&pointwise_fact, _verify_state)?;
                if pointwise_result.is_true() {
                    return Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "axiom_of_choice: general_cart is nonempty when every indexed factor is nonempty"
                                .to_string(),
                            vec![pointwise_result],
                        )
                        .into(),
                    );
                }
                Ok((StmtUnknown::new()).into())
            }
            Obj::FiniteSeqSet(fs) => {
                let codomain_nonempty = IsNonemptySetFact::new(
                    (*fs.set).clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let codomain_check = self.verify_non_equational_known_then_builtin_rules_only(
                    &codomain_nonempty,
                    _verify_state,
                )?;
                if codomain_check.is_true() {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "finite_seq_set_is_nonempty_when_codomain_set_is_nonempty".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            Obj::SeqSet(ss) => {
                let codomain_nonempty = IsNonemptySetFact::new(
                    (*ss.set).clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let codomain_check = self.verify_non_equational_known_then_builtin_rules_only(
                    &codomain_nonempty,
                    _verify_state,
                )?;
                if codomain_check.is_true() {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "seq_set_is_nonempty_when_codomain_set_is_nonempty".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            Obj::MatrixSet(ms) => {
                let codomain_nonempty = IsNonemptySetFact::new(
                    (*ms.set).clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let codomain_check = self.verify_non_equational_known_then_builtin_rules_only(
                    &codomain_nonempty,
                    _verify_state,
                )?;
                if codomain_check.is_true() {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_nonempty_set_fact.clone().into(),
                            "matrix_set_is_nonempty_when_codomain_set_is_nonempty".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            // A struct without filters is nonempty when every field type is nonempty.
            // Example: `struct Point: x R, y R` makes `&Point` nonempty from `R` and `R`.
            Obj::StructObj(struct_obj) => {
                let (def, param_to_arg_map) =
                    self.struct_header_param_to_arg_map(struct_obj, _verify_state)?;
                if !def.equivalent_facts.is_empty() {
                    return Ok((StmtUnknown::new()).into());
                }

                let mut step_results = Vec::with_capacity(def.fields.len());
                for (_, field_type) in def.fields.iter() {
                    let instantiated_field_type =
                        self.inst_obj(field_type, &param_to_arg_map, ParamObjType::DefHeader)?;
                    let field_nonempty: AtomicFact = IsNonemptySetFact::new(
                        instantiated_field_type,
                        is_nonempty_set_fact.line_file.clone(),
                    )
                    .into();
                    let field_result = self.verify_non_equational_known_then_builtin_rules_only(
                        &field_nonempty,
                        _verify_state,
                    )?;
                    if !field_result.is_true() {
                        return Ok((StmtUnknown::new()).into());
                    }
                    step_results.push(field_result);
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_nonempty_set_fact.clone().into(),
                        "struct_without_equivalent_facts_is_nonempty_when_all_field_types_are_nonempty"
                            .to_string(),
                        step_results,
                    ))
                    .into(),
                )
            }
            _ => {
                // Equality alias rule: a set alias is nonempty when it is already known equal
                // to a structural set whose nonemptiness is verified by builtin rules.
                // Example: from `T = fn(i closed_range(1, 3)) R`, prove `$is_nonempty_set(T)`.
                for equal_set in self
                    .get_all_obj_representatives_equal_to_given(&is_nonempty_set_fact.set)
                    .into_iter()
                {
                    if !obj_can_trigger_nonempty_structural_builtin(&equal_set) {
                        continue;
                    }
                    let equal_nonempty: AtomicFact =
                        IsNonemptySetFact::new(equal_set, is_nonempty_set_fact.line_file.clone())
                            .into();
                    let equal_result = self.verify_non_equational_known_then_builtin_rules_only(
                        &equal_nonempty,
                        _verify_state,
                    )?;
                    if equal_result.is_true() {
                        return Ok(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                                is_nonempty_set_fact.clone().into(),
                                InferResult::new(),
                                "nonempty_set_from_equal_structural_set".to_string(),
                                vec![equal_result],
                            )
                            .into(),
                        );
                    }
                }
                Ok((StmtUnknown::new()).into())
            }
        }
    }

    // A finite set with at least one element is nonempty.
    // Example: `$is_finite_set(S)`, `finite_set_size(S) >= 1` => `$is_nonempty_set(S)`.
    fn try_verify_nonempty_finite_set_from_positive_finite_set_size(
        &mut self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = is_nonempty_set_fact.line_file.clone();
        let finite: AtomicFact =
            IsFiniteSetFact::new(is_nonempty_set_fact.set.clone(), line_file.clone()).into();
        let finite_result =
            self.verify_non_equational_known_then_builtin_rules_only(&finite, verify_state)?;
        if !finite_result.is_true() {
            return Ok(None);
        }

        let finite_set_size_at_least_one: AtomicFact = GreaterEqualFact::new(
            FiniteSetSize::new(is_nonempty_set_fact.set.clone()).into(),
            Number::new("1".to_string()).into(),
            line_file,
        )
        .into();
        let finite_set_size_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(
                &finite_set_size_at_least_one,
            )?;
        if !finite_set_size_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                is_nonempty_set_fact.clone().into(),
                InferResult::new(),
                "nonempty_finite_set_from_positive_finite_set_size".to_string(),
                vec![finite_result, finite_set_size_result],
            )
            .into(),
        ))
    }

    pub fn _verify_is_finite_set_fact_with_builtin_rules(
        &mut self,
        is_finite_set_fact: &IsFiniteSetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match &is_finite_set_fact.set {
            Obj::ListSet(_) => Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    is_finite_set_fact.clone().into(),
                    "list_set_finite".to_string(),
                    Vec::new(),
                ))
                .into(),
            ),
            Obj::ClosedRange(_) => Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    is_finite_set_fact.clone().into(),
                    "closed_range_is_finite_set".to_string(),
                    Vec::new(),
                ))
                .into(),
            ),
            Obj::Range(_) => Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    is_finite_set_fact.clone().into(),
                    "range_is_finite_set".to_string(),
                    Vec::new(),
                ))
                .into(),
            ),
            // The image of a finite unary domain under a function is finite.
            // Example: from `a fn(x 1...3) R`, prove `$is_finite_set(fn_range(a))`.
            Obj::FnRange(fn_range) => {
                let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
                    return Ok((StmtUnknown::new()).into());
                };
                if body.params_def_with_set.number_of_params() != 1 {
                    return Ok((StmtUnknown::new()).into());
                }
                let Some(domain) = body.params_def_with_set.first() else {
                    return Ok((StmtUnknown::new()).into());
                };
                let domain_finite: AtomicFact = IsFiniteSetFact::new(
                    domain.set_obj().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let domain_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &domain_finite,
                    _verify_state,
                )?;
                if domain_result.is_true() {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_finite_set_fact.clone().into(),
                            "fn_range_is_finite_set_when_domain_is_finite_set".to_string(),
                            vec![domain_result],
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            // The union of two finite sets is finite.
            // Example: from `$is_finite_set(A)` and `$is_finite_set(B)`, prove
            // `$is_finite_set(union(A, B))`.
            Obj::Union(union) => {
                let left_finite: AtomicFact = IsFiniteSetFact::new(
                    union.left.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let right_finite: AtomicFact = IsFiniteSetFact::new(
                    union.right.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let left_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &left_finite,
                    _verify_state,
                )?;
                if !left_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                let right_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &right_finite,
                    _verify_state,
                )?;
                if !right_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_finite_set_fact.clone().into(),
                        "union_is_finite_set_when_both_sides_are_finite_set".to_string(),
                        vec![left_result, right_result],
                    ))
                    .into(),
                )
            }
            // The intersection of two finite sets is finite.
            // Example: from `$is_finite_set(A)` and `$is_finite_set(B)`, prove
            // `$is_finite_set(intersect(A, B))`.
            Obj::Intersect(intersect) => {
                let left_finite: AtomicFact = IsFiniteSetFact::new(
                    intersect.left.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let right_finite: AtomicFact = IsFiniteSetFact::new(
                    intersect.right.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let left_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &left_finite,
                    _verify_state,
                )?;
                if !left_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                let right_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &right_finite,
                    _verify_state,
                )?;
                if !right_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_finite_set_fact.clone().into(),
                        "intersect_is_finite_set_when_both_sides_are_finite_set".to_string(),
                        vec![left_result, right_result],
                    ))
                    .into(),
                )
            }
            // Finite set difference: a subset of a finite set is finite.
            // Example: from `$is_finite_set(A)`, prove `$is_finite_set(set_minus(A, B))`.
            Obj::SetMinus(set_minus) => {
                let left_finite: AtomicFact = IsFiniteSetFact::new(
                    set_minus.left.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let left_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &left_finite,
                    _verify_state,
                )?;
                if !left_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_finite_set_fact.clone().into(),
                        "set_minus_is_finite_set_when_left_side_is_finite_set".to_string(),
                        vec![left_result],
                    ))
                    .into(),
                )
            }
            // Symmetric difference is finite when both operands are finite.
            // Example: from `$is_finite_set(A)` and `$is_finite_set(B)`, prove
            // `$is_finite_set(set_diff(A, B))`.
            Obj::SetDiff(set_diff) => {
                let left_finite: AtomicFact = IsFiniteSetFact::new(
                    set_diff.left.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let right_finite: AtomicFact = IsFiniteSetFact::new(
                    set_diff.right.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let left_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &left_finite,
                    _verify_state,
                )?;
                if !left_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                let right_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &right_finite,
                    _verify_state,
                )?;
                if !right_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_finite_set_fact.clone().into(),
                        "set_diff_is_finite_set_when_both_sides_are_finite_set".to_string(),
                        vec![left_result, right_result],
                    ))
                    .into(),
                )
            }
            // Power set of a finite set is finite.
            // Example: from `$is_finite_set(S)`, prove `$is_finite_set(power_set(S))`.
            Obj::PowerSet(power_set) => {
                let base_finite: AtomicFact = IsFiniteSetFact::new(
                    power_set.set.as_ref().clone(),
                    is_finite_set_fact.line_file.clone(),
                )
                .into();
                let base_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &base_finite,
                    _verify_state,
                )?;
                if !base_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_finite_set_fact.clone().into(),
                        "power_set_is_finite_set_when_base_is_finite_set".to_string(),
                        vec![base_result],
                    ))
                    .into(),
                )
            }
            // Finite Cartesian product: if each factor is finite, the product set is finite.
            // Example: from `$is_finite_set(A)` and `$is_finite_set(B)`, prove
            // `$is_finite_set(cart(A, B))`.
            Obj::Cart(cart) => {
                let mut step_results = Vec::new();
                for arg in cart.args.iter() {
                    let factor_finite: AtomicFact = IsFiniteSetFact::new(
                        arg.as_ref().clone(),
                        is_finite_set_fact.line_file.clone(),
                    )
                    .into();
                    let factor_result = self.verify_non_equational_known_then_builtin_rules_only(
                        &factor_finite,
                        _verify_state,
                    )?;
                    if !factor_result.is_true() {
                        return Ok((StmtUnknown::new()).into());
                    }
                    step_results.push(factor_result);
                }
                Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_finite_set_fact.clone().into(),
                        "cart_is_finite_set_when_all_factors_are_finite_set".to_string(),
                        step_results,
                    ))
                    .into(),
                )
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub fn _verify_not_is_finite_set_fact_with_builtin_rules(
        &mut self,
        not_is_finite_set_fact: &NotIsFiniteSetFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Removing a finite set from an infinite set leaves an infinite set.
        // Example: from `not $is_finite_set(X)` and `$is_finite_set(s)`, prove
        // `not $is_finite_set(set_minus(X, s))`.
        let Obj::SetMinus(set_minus) = &not_is_finite_set_fact.set else {
            return Ok((StmtUnknown::new()).into());
        };

        let left_infinite: AtomicFact = NotIsFiniteSetFact::new(
            set_minus.left.as_ref().clone(),
            not_is_finite_set_fact.line_file.clone(),
        )
        .into();
        let left_result =
            self.verify_non_equational_known_then_builtin_rules_only(&left_infinite, verify_state)?;
        if !left_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let right_finite: AtomicFact = IsFiniteSetFact::new(
            set_minus.right.as_ref().clone(),
            not_is_finite_set_fact.line_file.clone(),
        )
        .into();
        let right_result =
            self.verify_non_equational_known_then_builtin_rules_only(&right_finite, verify_state)?;
        if !right_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                not_is_finite_set_fact.clone().into(),
                "set_minus_is_infinite_when_left_side_is_infinite_and_right_side_is_finite"
                    .to_string(),
                vec![left_result, right_result],
            )
            .into(),
        )
    }

    pub fn _verify_is_cart_fact_with_builtin_rules(
        &mut self,
        is_cart_fact: &IsCartFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match &is_cart_fact.set {
            Obj::Cart(_) => {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_cart_fact.clone().into(),
                        "any `cart` object is a cart".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub fn _verify_is_tuple_fact_with_builtin_rules(
        &mut self,
        is_tuple_fact: &IsTupleFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match &is_tuple_fact.set {
            Obj::Tuple(t) => {
                if t.args.len() < 2 {
                    return Ok((StmtUnknown::new()).into());
                }
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        is_tuple_fact.clone().into(),
                        "any `cart_dim` object is a cart_dim".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
            _ => {
                if let Some((_, _, _)) = self
                    .top_level_env()
                    .known_objs_equal_to_tuple
                    .get(&is_tuple_fact.set.to_string())
                {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            is_tuple_fact.clone().into(),
                            "it is a known tuple".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }

                Ok((StmtUnknown::new()).into())
            }
        }
    }

    pub fn _verify_not_is_nonempty_set_fact_with_builtin_rules(
        &mut self,
        not_is_nonempty_set_fact: &NotIsNonemptySetFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::ListSet(list_set) = &not_is_nonempty_set_fact.set {
            if list_set.list.is_empty() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_is_nonempty_set_fact.clone().into(),
                        "list_set_empty".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }
        // A finite set of size zero has no member.
        // Example: `finite_set_size(S) = 0` => `not $is_nonempty_set(S)`.
        let finite_set_size: Obj = FiniteSetSize::new(not_is_nonempty_set_fact.set.clone()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let size_zero_result = self.verify_objs_are_equal_known_only(
            &finite_set_size,
            &zero,
            not_is_nonempty_set_fact.line_file.clone(),
        );
        if size_zero_result.is_true() {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    not_is_nonempty_set_fact.clone().into(),
                    InferResult::new(),
                    "finite_set_size_zero_is_not_nonempty".to_string(),
                    vec![size_zero_result],
                )
                .into(),
            );
        }
        // Empty set rule: `not $is_nonempty_set(S)` follows from known `S = {}`.
        // Example: after `S = {}`, prove `not $is_nonempty_set(S)`.
        let empty_set: Obj = ListSet::new(vec![]).into();
        if self
            .objs_have_same_known_equality_rc_in_some_env(&not_is_nonempty_set_fact.set, &empty_set)
        {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_is_nonempty_set_fact.clone().into(),
                    "not_nonempty_set_from_equal_empty_set".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        if let Obj::ClosedRange(closed_range) = &not_is_nonempty_set_fact.set {
            // Integer closed interval `{x in Z | lo <= x <= hi}` is empty from a known
            // `hi < lo` fact.
            // Example: under `b < a`, prove `not $is_nonempty_set(closed_range(a, b))`.
            let lt: AtomicFact = LessFact::new(
                closed_range.end.as_ref().clone(),
                closed_range.start.as_ref().clone(),
                not_is_nonempty_set_fact.line_file.clone(),
            )
            .into();
            let lt_ok =
                self.verify_non_equational_known_then_builtin_rules_only(&lt, verify_state)?;
            if lt_ok.is_true() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_is_nonempty_set_fact.clone().into(),
                        "closed_range_empty_when_end_lt_start".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }
        if let Obj::Range(range) = &not_is_nonempty_set_fact.set {
            // Integer half-open interval `{x in Z | lo <= x < hi}` is empty from a
            // known `hi <= lo` fact. Example: `range(0, 0) = {}`.
            let le: AtomicFact = LessEqualFact::new(
                range.end.as_ref().clone(),
                range.start.as_ref().clone(),
                not_is_nonempty_set_fact.line_file.clone(),
            )
            .into();
            let le_ok =
                self.verify_non_equational_known_then_builtin_rules_only(&le, verify_state)?;
            if le_ok.is_true() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_is_nonempty_set_fact.clone().into(),
                        "range_empty_when_end_le_start".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }
        Ok((StmtUnknown::new()).into())
    }
}

fn general_cart_global_family_nonempty_fact(
    general_cart: &GeneralCart,
    source_fact: &IsNonemptySetFact,
) -> Fact {
    let param_name = "X".to_string();
    let param_obj = obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Forall);
    ForallFact::new(
        ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![param_name],
            ParamType::Obj(general_cart.family_set.as_ref().clone()),
        )]),
        vec![],
        vec![IsNonemptySetFact::new(param_obj, source_fact.line_file.clone()).into()],
        source_fact.line_file.clone(),
    )
    .expect("general_cart global nonempty forall has a fresh local parameter")
    .into()
}

fn general_cart_pointwise_family_nonempty_fact(
    general_cart: &GeneralCart,
    source_fact: &IsNonemptySetFact,
) -> Result<Option<Fact>, RuntimeError> {
    let Some(head) = FnObjHead::from_callable_obj(general_cart.family_fn.as_ref().clone()) else {
        return Ok(None);
    };
    let param_name = "alpha".to_string();
    let param_obj = obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Forall);
    let factor: Obj = FnObj::new(head, vec![vec![Box::new(param_obj.clone())]]).into();
    Ok(Some(
        ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![param_name],
                ParamType::Obj(general_cart.index_set.as_ref().clone()),
            )]),
            vec![],
            vec![IsNonemptySetFact::new(factor, source_fact.line_file.clone()).into()],
            source_fact.line_file.clone(),
        )?
        .into(),
    ))
}

fn obj_can_trigger_nonempty_structural_builtin(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::StandardSet(_)
            | Obj::ListSet(_)
            | Obj::PowerSet(_)
            | Obj::ClosedRange(_)
            | Obj::IntervalObj(_)
            | Obj::OneSideInfinityIntervalObj(_)
            | Obj::Union(_)
            | Obj::Cart(_)
            | Obj::GeneralCart(_)
            | Obj::FnSet(_)
            | Obj::AnonymousFn(_)
            | Obj::FiniteSeqSet(_)
            | Obj::SeqSet(_)
            | Obj::MatrixSet(_)
            | Obj::StructObj(_)
    )
}
