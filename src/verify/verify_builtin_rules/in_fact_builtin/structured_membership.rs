use super::*;

impl Runtime {
    // `{x S : …} ⊆ S` always. If `S ⊆ T` then `{x S : …} ⊆ T`, so `{x S : …} ∈ 𝒫(T)`.
    // Example: from `N $subset Z`, deduce `{x N: x = x} $in power_set(Z)` once that subset is known.
    pub(super) fn verify_in_fact_set_builder_in_power_set_via_param_subset(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let subset_fact = SubsetFact::new(
            (*set_builder.param_set).clone(),
            base_set.clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let verify_subset_result =
            self.verify_atomic_fact_by_known_atomic_or_builtin_only(&subset_fact, verify_state)?;
        if !verify_subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(verify_subset_result.infer_result());
        let stmt = in_fact.clone().into();
        infer_result.new_fact(&stmt);
        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
            stmt.clone(),
            infer_result,
            VerifiedByResult::builtin_rule(
                "set_builder in power_set: param_set subset of base implies builder defines a subset of base"
                    .to_string(),
                stmt,
            ),
        ))
        .into())
    }

    pub(super) fn verify_in_fact_list_set_in_power_set_defines_membership(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let mut infer_result = InferResult::new();
        for element_box in list_set.list.iter() {
            let element_obj = *element_box.clone();
            let element_in_base_fact =
                InFact::new(element_obj, base_set.clone(), in_fact.line_file.clone()).into();
            let verify_one_element_result = self
                .verify_atomic_fact_by_known_atomic_or_builtin_only(
                    &element_in_base_fact,
                    verify_state,
                )?;
            if !verify_one_element_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            infer_result.new_infer_result_inside(verify_one_element_result.infer_result());
        }
        let stmt = in_fact.clone().into();
        infer_result.new_fact(&stmt);
        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
            stmt.clone(),
            infer_result,
            VerifiedByResult::builtin_rule(
                "list_set in power_set: each element is in the base set".to_string(),
                stmt,
            ),
        ))
        .into())
    }

    pub(super) fn verify_in_fact_by_equal_to_one_element_in_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let equality_or_result =
            self.verify_in_fact_by_equality_or_for_list_set(in_fact, list_set, verify_state)?;
        if equality_or_result.is_true() {
            return Ok(equality_or_result);
        }

        for current_element_in_list_set in list_set.list.iter() {
            let equal_fact_verify_result = self.verify_objs_are_equal_known_only(
                &in_fact.element,
                current_element_in_list_set.as_ref(),
                in_fact.line_file.clone(),
            );
            if equal_fact_verify_result.is_true() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }
        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn verify_in_fact_by_equality_or_for_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if list_set.list.is_empty() {
            return Ok((StmtUnknown::new()).into());
        }

        let mut left_equal_facts = Vec::with_capacity(list_set.list.len());
        let mut right_equal_facts = Vec::with_capacity(list_set.list.len());
        for current_element_in_list_set in list_set.list.iter() {
            left_equal_facts.push(AndChainAtomicFact::AtomicFact(
                EqualFact::new(
                    in_fact.element.clone(),
                    *current_element_in_list_set.clone(),
                    in_fact.line_file.clone(),
                )
                .into(),
            ));
            right_equal_facts.push(AndChainAtomicFact::AtomicFact(
                EqualFact::new(
                    *current_element_in_list_set.clone(),
                    in_fact.element.clone(),
                    in_fact.line_file.clone(),
                )
                .into(),
            ));
        }

        let candidate_or_facts = [
            OrFact::new(left_equal_facts, in_fact.line_file.clone()),
            OrFact::new(right_equal_facts, in_fact.line_file.clone()),
        ];

        for candidate_or_fact in candidate_or_facts {
            let candidate_result = self
                .verify_or_fact_known_then_builtin_rules_only(&candidate_or_fact, verify_state)?;
            if candidate_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        in_fact.clone().into(),
                        InferResult::from_fact(&in_fact.clone().into()),
                        "list_set membership: equality with one listed element".to_string(),
                        vec![candidate_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn verify_not_in_fact_by_not_equal_to_every_element_in_list_set(
        &mut self,
        not_in_fact: &NotInFact,
        list_set: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        for current_element_in_list_set in list_set.list.iter() {
            let not_equal_fact = NotEqualFact::new(
                not_in_fact.element.clone(),
                *current_element_in_list_set.clone(),
                not_in_fact.line_file.clone(),
            )
            .into();
            let not_equal_fact_verify_result = self
                .verify_atomic_fact_known_then_builtin_rules_only(&not_equal_fact, verify_state)?;
            if !not_equal_fact_verify_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                not_in_fact.clone().into(),
                format!(
                    "{} is not equal to every element in list_set {}",
                    not_in_fact.element, not_in_fact.set
                ),
                Vec::new(),
            ))
            .into(),
        )
    }

    pub(super) fn standard_subset_set_objs_for_target_set(
        target_set_obj: &Obj,
    ) -> Option<Vec<Obj>> {
        match target_set_obj {
            Obj::StandardSet(StandardSet::NPos) => Some(vec![]),
            Obj::StandardSet(StandardSet::N) => Some(vec![StandardSet::NPos.into()]),
            Obj::StandardSet(StandardSet::ZNeg) => Some(vec![]),
            Obj::StandardSet(StandardSet::ZNz) => {
                Some(vec![StandardSet::NPos.into(), StandardSet::ZNeg.into()])
            }
            Obj::StandardSet(StandardSet::Z) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
            ]),
            Obj::StandardSet(StandardSet::QPos) => Some(vec![StandardSet::NPos.into()]),
            Obj::StandardSet(StandardSet::QNeg) => Some(vec![StandardSet::ZNeg.into()]),
            Obj::StandardSet(StandardSet::QNz) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::Q) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::Z.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
            ]),
            Obj::StandardSet(StandardSet::RPos) => {
                Some(vec![StandardSet::NPos.into(), StandardSet::QPos.into()])
            }
            Obj::StandardSet(StandardSet::RNeg) => {
                Some(vec![StandardSet::ZNeg.into(), StandardSet::QNeg.into()])
            }
            Obj::StandardSet(StandardSet::RNz) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
                StandardSet::RPos.into(),
                StandardSet::RNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::R) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::Z.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
                StandardSet::Q.into(),
                StandardSet::RPos.into(),
                StandardSet::RNeg.into(),
                StandardSet::RNz.into(),
            ]),
            _ => None,
        }
    }

    // If the env already has `element $in fn_def` (from `known_objs_in_fn_sets`), compare to the RHS `fn ...`.
    pub(super) fn verify_in_fact_element_in_fn_set_by_stored_definition(
        &mut self,
        element: &Obj,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(stored_fn_set) = self.get_cloned_object_in_fn_set(element) else {
            return Ok((StmtUnknown::new()).into());
        };
        if stored_fn_set.to_string() == expected_fn_set.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "fn membership: stored fn signature matches RHS".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let flat_stored =
            ParamGroupWithSet::collect_param_names(&stored_fn_set.params_def_with_set);
        let flat_expected =
            ParamGroupWithSet::collect_param_names(&expected_fn_set.body.params_def_with_set);
        if flat_stored.len() != flat_expected.len() {
            return Ok((StmtUnknown::new()).into());
        }
        let shared_names = self.generate_random_unused_names(flat_stored.len());
        let stored_norm =
            self.fn_set_alpha_renamed_for_display_compare(&stored_fn_set, &shared_names)?;
        let expected_norm =
            self.fn_set_alpha_renamed_for_display_compare(&expected_fn_set.body, &shared_names)?;
        if stored_norm.to_string() == expected_norm.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "fn membership: stored fn signature matches RHS (alpha-renamed parameters)"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        Ok((StmtUnknown::new()).into())
    }

    /// `anon $in S` when `S` is a function space [`FnSet`] and the anonymous function's
    /// [`FnSetBody`] (params, dom facts, return set) matches `S` (same as comparing `S` to a
    /// [`FnSet`] built from the anon's body without the braced `equal_to`).
    pub(super) fn verify_in_fact_anonymous_fn_signature_matches_fn_set(
        &mut self,
        anon: &AnonymousFn,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let signature_from_anon = FnSet::new(
            anon.body.params_def_with_set.clone(),
            anon.body.dom_facts.clone(),
            (*anon.body.ret_set).clone(),
        )?;
        if signature_from_anon.to_string() == expected_fn_set.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature (params, dom, co-domain) matches `fn` set"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let flat_a =
            ParamGroupWithSet::collect_param_names(&signature_from_anon.body.params_def_with_set);
        let flat_e =
            ParamGroupWithSet::collect_param_names(&expected_fn_set.body.params_def_with_set);
        if flat_a.len() != flat_e.len() {
            return Ok((StmtUnknown::new()).into());
        }
        let shared_names = self.generate_random_unused_names(flat_a.len());
        let a_norm = self
            .fn_set_alpha_renamed_for_display_compare(&signature_from_anon.body, &shared_names)?;
        let e_norm =
            self.fn_set_alpha_renamed_for_display_compare(&expected_fn_set.body, &shared_names)?;
        if a_norm.to_string() == e_norm.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature matches `fn` set (alpha-renamed parameters)"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // Function-space transport across propositionally equal parameter sets.
        // Example: `J = A` permits `fn(x J) R {f(x)}` as a member of `fn(x A) R`.
        let signature_equality = self.verify_fn_set_with_params_equality_by_builtin_rules(
            &signature_from_anon,
            expected_fn_set,
            in_fact.line_file.clone(),
            verify_state,
        )?;
        if signature_equality.is_true() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature matches `fn` set through propositionally equal parameter sets"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        Ok((StmtUnknown::new()).into())
    }

    // If every entry of `[a, b, ...]` is in `S`, then applying it at a valid index gives an element of `S`.
    // Example: `[1, 2, 3](i) $in R` follows from `i $in N_pos`, `i <= 3`, and each entry in `R`.
    pub(super) fn verify_in_fact_finite_seq_literal_application_in_set(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Obj::FnObj(fn_obj) = &in_fact.element else {
            return Ok((StmtUnknown::new()).into());
        };
        let FnObjHead::FiniteSeqListObj(list) = fn_obj.head.as_ref() else {
            return Ok((StmtUnknown::new()).into());
        };
        if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
            return Ok((StmtUnknown::new()).into());
        };

        let index_obj = fn_obj.body[0][0].as_ref().clone();
        let mut step_results = Vec::new();

        let index_in_n_pos: AtomicFact = InFact::new(
            index_obj.clone(),
            StandardSet::NPos.into(),
            in_fact.line_file.clone(),
        )
        .into();
        let index_in_n_pos_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&index_in_n_pos, verify_state)?;
        if !index_in_n_pos_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(index_in_n_pos_result);

        let list_len_obj: Obj = Number::new(list.objs.len().to_string()).into();
        let index_in_range: AtomicFact =
            LessEqualFact::new(index_obj, list_len_obj, in_fact.line_file.clone()).into();
        let index_in_range_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&index_in_range, verify_state)?;
        if !index_in_range_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(index_in_range_result);

        for element in list.objs.iter() {
            let element_in_target_set: AtomicFact = InFact::new(
                element.as_ref().clone(),
                target_set_obj.clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let result = self.verify_atomic_fact_known_then_builtin_rules_only(
                &element_in_target_set,
                verify_state,
            )?;
            if !result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(result);
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                format!(
                    "finite sequence literal application is in {}",
                    target_set_obj
                ),
                step_results,
            ))
            .into(),
        )
    }

    // If `x $in cart({a, b}, {c, d})` is known, then `x[1]` ranges over `{a, b}`.
    // Example: if every element of `{a, b}` is in `R`, prove `x[1] $in R`.
    pub(super) fn verify_in_fact_obj_at_index_in_standard_set_by_cart_factor_list_set(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Obj::StandardSet(_) = target_set_obj else {
            return Ok((StmtUnknown::new()).into());
        };
        let Obj::ObjAtIndex(obj_at_index) = &in_fact.element else {
            return Ok((StmtUnknown::new()).into());
        };
        let Some(cart) = self.get_object_equal_to_cart(&obj_at_index.obj.to_string()) else {
            return Ok((StmtUnknown::new()).into());
        };
        let Some(index_number) = self.resolve_obj_to_number(&obj_at_index.index) else {
            return Ok((StmtUnknown::new()).into());
        };
        let Ok(one_based_index) = index_number.normalized_value.parse::<usize>() else {
            return Ok((StmtUnknown::new()).into());
        };
        if one_based_index == 0 || one_based_index > cart.args.len() {
            return Ok((StmtUnknown::new()).into());
        }

        let factor = cart.args[one_based_index - 1].as_ref();
        let Obj::ListSet(list_set) = factor else {
            return Ok((StmtUnknown::new()).into());
        };

        let mut step_results = Vec::new();
        for element in list_set.list.iter() {
            let element_in_target_set: AtomicFact = InFact::new(
                element.as_ref().clone(),
                target_set_obj.clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let result = self.verify_atomic_fact_known_then_builtin_rules_only(
                &element_in_target_set,
                verify_state,
            )?;
            if !result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(result);
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                format!(
                    "cart projection list_set elements are all in {}",
                    target_set_obj
                ),
                step_results,
            ))
            .into(),
        )
    }

    pub(super) fn verify_in_fact_by_known_standard_subset_membership(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
    ) -> Result<StmtResult, RuntimeError> {
        let standard_subset_set_objs =
            match Self::standard_subset_set_objs_for_target_set(target_set_obj) {
                Some(standard_subset_set_objs) => standard_subset_set_objs,
                None => return Ok((StmtUnknown::new()).into()),
            };
        for standard_subset_set_obj in standard_subset_set_objs.iter() {
            let in_fact_into_standard_subset = InFact::new(
                in_fact.element.clone(),
                standard_subset_set_obj.clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
                &in_fact_into_standard_subset,
            )?;
            if verify_result.is_true() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, standard_subset_set_obj, target_set_obj
                        ),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }
        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn verify_not_in_z_for_resolved_numeric_div(
        &self,
        not_in_fact: &NotInFact,
    ) -> Option<StmtResult> {
        let (numerator, denominator) = self.resolved_numeric_div_operands(&not_in_fact.element)?;
        if !number_is_in_z(&numerator) || !number_is_in_z_nz(&denominator) {
            return None;
        }

        let remainder_obj: Obj = Mod::new(numerator.into(), denominator.into()).into();
        let remainder = self.resolve_obj_to_number_resolved(&remainder_obj)?;
        if matches!(
            compare_normalized_number_str_to_zero(&remainder.normalized_value),
            NumberCompareResult::Equal
        ) {
            return None;
        }

        Some(not_in_fact_verified_by_builtin_rules_result(
            not_in_fact,
            "numeric division not in Z: resolved numerator % denominator != 0",
        ))
    }

    pub(super) fn resolved_numeric_div_operands(&self, obj: &Obj) -> Option<(Number, Number)> {
        if let Some(operands) = self.numeric_div_operands_after_resolve(obj) {
            return Some(operands);
        }

        let obj_key = obj.to_string();
        for env in self.iter_environments_from_top() {
            let Some((_, equal_objs)) = env.known_equality.get(&obj_key) else {
                continue;
            };
            for equal_obj in equal_objs.iter() {
                if let Some(operands) = self.numeric_div_operands_after_resolve(equal_obj) {
                    return Some(operands);
                }
            }
        }
        None
    }

    pub(super) fn numeric_div_operands_after_resolve(&self, obj: &Obj) -> Option<(Number, Number)> {
        let resolved = self.resolve_obj(obj);
        let Obj::Div(div) = resolved else {
            return None;
        };
        let numerator = self.resolve_obj_to_number_resolved(div.left.as_ref())?;
        let denominator = self.resolve_obj_to_number_resolved(div.right.as_ref())?;
        Some((numerator, denominator))
    }
}
