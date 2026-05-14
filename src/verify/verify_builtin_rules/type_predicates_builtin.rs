use crate::prelude::*;

impl Runtime {
    pub fn _verify_is_nonempty_set_fact_with_builtin_rules(
        &mut self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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
            // Integer closed interval `{x in Z | lo <= x <= hi}` is nonempty iff `lo <= hi`.
            // Numeric well-defined `closed_range` requires this order when endpoints are concrete;
            // otherwise we still need a provable `lo <= hi` (e.g. from the environment).
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
            Obj::Cart(cart) => {
                for arg_obj in &cart.args {
                    let is_nonempty_set_result = self
                        .verify_non_equational_atomic_fact_with_builtin_rules(
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
                let ret_check = self.verify_non_equational_atomic_fact_with_builtin_rules(
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
                let ret_check = self.verify_non_equational_atomic_fact_with_builtin_rules(
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
            Obj::FiniteSeqSet(fs) => {
                let codomain_nonempty = IsNonemptySetFact::new(
                    (*fs.set).clone(),
                    is_nonempty_set_fact.line_file.clone(),
                )
                .into();
                let codomain_check = self.verify_non_equational_atomic_fact_with_builtin_rules(
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
                let codomain_check = self.verify_non_equational_atomic_fact_with_builtin_rules(
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
                let codomain_check = self.verify_non_equational_atomic_fact_with_builtin_rules(
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
                    let field_result = self.verify_non_equational_atomic_fact(
                        &field_nonempty,
                        _verify_state,
                        true,
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
            _ => Ok((StmtUnknown::new()).into()),
        }
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
                let left_result =
                    self.verify_non_equational_atomic_fact(&left_finite, _verify_state, true)?;
                if !left_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                let right_result =
                    self.verify_non_equational_atomic_fact(&right_finite, _verify_state, true)?;
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
                let left_result =
                    self.verify_non_equational_atomic_fact(&left_finite, _verify_state, true)?;
                if !left_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                let right_result =
                    self.verify_non_equational_atomic_fact(&right_finite, _verify_state, true)?;
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
                    let factor_result = self.verify_non_equational_atomic_fact(
                        &factor_finite,
                        _verify_state,
                        true,
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
        _verify_state: &VerifyState,
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
        Ok((StmtUnknown::new()).into())
    }
}
