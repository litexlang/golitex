use super::*;

impl Runtime {
    /// A definition-owned field projection has the carrier defined by its
    /// owning struct.  The receiver's struct membership remains an explicit
    /// proof premise, so later unrelated membership facts cannot select or
    /// change a field owner.
    pub(super) fn verify_in_fact_struct_field_in_definition_carrier(
        &mut self,
        in_fact: &InFact,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let definition_carrier =
            self.instantiated_struct_field_type_after_well_defined(field_access)?;
        let carrier_equality_fact = self.new_equal_fact_from_refs(
            &definition_carrier,
            &in_fact.set,
            in_fact.line_file.clone(),
        );
        let carrier_equality_proof =
            self.verify_equal_fact_by_known_equality(&carrier_equality_fact);
        let carrier_equality_atomic: AtomicFact = carrier_equality_fact.into();
        let carrier_equality = self.complete_atomic_fact_proof_result(
            &carrier_equality_atomic,
            carrier_equality_proof,
            builtin_state.verify_state(),
        )?;
        let standard_widening = matches!(
            (&definition_carrier, &in_fact.set),
            (Obj::StandardSet(defined), Obj::StandardSet(target)) if defined.is_subset_eq(target)
        );
        if !carrier_equality.is_success() && !standard_widening {
            return Ok((UnknownGenericStmtResult::new()).into());
        }

        let struct_obj = self.direct_struct_owner_carrier_for_field_access(
            field_access,
            in_fact.line_file.clone(),
        )?;
        let receiver_membership: AtomicFact = self
            .new_in_fact(
                (*field_access.obj).clone(),
                struct_obj.into(),
                in_fact.line_file.clone(),
            )
            .into();
        let Some(receiver_result) = self
            .try_verify_atomic_fact_as_builtin_rule_premise(&receiver_membership, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        let mut steps = vec![receiver_result];
        if carrier_equality.is_success() {
            steps.push(carrier_equality);
        }
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "definition-owned struct field has its instantiated defined carrier".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactStructFieldInDefinitionCarrier,
                ),
                steps,
            )
            .into(),
        )
    }

    pub(super) fn verify_in_fact_literal_tuple_projection_in_set(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let (tuple, index) = match &in_fact.element {
            Obj::Proj(projection) => {
                let Obj::Tuple(tuple) = projection.set.as_ref() else {
                    return Ok(UnknownGenericStmtResult::new().into());
                };
                (tuple, projection.dim.as_ref())
            }
            Obj::ObjAtIndex(obj_at_index) => {
                let Obj::Tuple(tuple) = obj_at_index.obj.as_ref() else {
                    return Ok(UnknownGenericStmtResult::new().into());
                };
                (tuple, obj_at_index.index.as_ref())
            }
            _ => return Ok(UnknownGenericStmtResult::new().into()),
        };
        let Some(index_number) = self.resolve_obj_to_number(index) else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        let Ok(one_based_index) = index_number.normalized_value.parse::<usize>() else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        if one_based_index == 0 || one_based_index > tuple.args.len() {
            return Ok(UnknownGenericStmtResult::new().into());
        }

        let selected = tuple.args[one_based_index - 1].as_ref().clone();
        let selected_membership: AtomicFact = self
            .new_in_fact(
                selected.clone(),
                target_set_obj.clone(),
                in_fact.line_file.clone(),
            )
            .into();
        let mut selected_result = self
            .try_verify_atomic_fact_as_builtin_rule_premise(&selected_membership, builtin_state)?;
        if selected_result.is_none() && matches!(target_set_obj, Obj::StandardSet(StandardSet::R)) {
            if let Some(real_steps) = self.verify_objects_are_known_reals_in_builtin(
                &[&selected],
                &in_fact.line_file,
                builtin_state,
            )? {
                let proof =
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        selected_membership.clone().into(),
                        "selected literal tuple component has a real carrier".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactLiteralTupleProjectionInSet01),
                        real_steps,
                    )
                    .into();
                selected_result = Some(self.complete_atomic_fact_proof_result(
                    &selected_membership,
                    proof,
                    builtin_state.verify_state(),
                )?);
            }
        }
        // A refined real membership can be widened to `C` without resolving
        // the selected object.  This is important for literal tuple
        // projections whose component is a transparent object definition:
        // the exact `x $in R` fact is replayable, while resolving `x` to a
        // numeric literal may not have a transport certificate.
        if selected_result.is_none() && matches!(target_set_obj, Obj::StandardSet(StandardSet::C)) {
            let real_membership: AtomicFact = self
                .new_in_fact(
                    selected.clone(),
                    StandardSet::R.into(),
                    in_fact.line_file.clone(),
                )
                .into();
            let real_proof = match self
                .verification_result_from_known_fact_cache(&real_membership.clone().into())
            {
                Some(proof) => proof,
                None => self.verify_non_equational_atomic_fact_with_zero_premise_verification(
                    &real_membership,
                )?,
            };

            if let Some(real_result) = self.complete_proven_fact_candidate(
                real_membership.into(),
                real_proof,
                builtin_state.verify_state(),
            )? {
                let widened_proof = SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    selected_membership.clone().into(),
                    "real membership widens to complex membership".to_string(),
                    BuiltinRuleEvidence::StandardSetMembershipProjection,
                    vec![real_result],
                )
                .into();
                selected_result = Some(self.complete_atomic_fact_proof_result(
                    &selected_membership,
                    widened_proof,
                    builtin_state.verify_state(),
                )?);
            }
        }
        let Some(selected_result) = selected_result else {
            return Ok(UnknownGenericStmtResult::new().into());
        };

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "literal tuple projection inherits the selected component carrier".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactLiteralTupleProjectionInSet02,
                ),
                vec![selected_result],
            )
            .into(),
        )
    }

    // `{x S : …} ⊆ S` always. If `S ⊆ T` then `{x S : …} ⊆ T`, so `{x S : …} ∈ 𝒫(T)`.
    // Example: from `N $subset Z`, deduce `{x N: x = x} $in power_set(Z)` once that subset is known.
    pub(super) fn verify_in_fact_set_builder_in_power_set_via_param_subset(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
        power_set: &PowerSet,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let subset_fact: AtomicFact = self
            .new_subset_fact(
                (*set_builder.param_set).clone(),
                base_set.clone(),
                in_fact.line_file.clone(),
            )
            .into();
        let verify_subset_result = match (&*set_builder.param_set, base_set) {
            (Obj::StandardSet(left), Obj::StandardSet(right)) if left.is_subset_eq(right) => {
                let proof = SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    subset_fact.clone().into(),
                    "standard_set_subset".to_string(),
                    BuiltinRuleEvidence::StandardSetSubset,
                    Vec::new(),
                )
                .into();
                Some(self.complete_atomic_fact_proof_result(
                    &subset_fact,
                    proof,
                    builtin_state.verify_state(),
                )?)
            }
            (left, right) if objs_equal_with_nested_binder_alpha_equivalence(left, right) => {
                let proof = SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    subset_fact.clone().into(),
                    "subset reflexivity".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactSetBuilderInPowerSetViaParamSubset01,
                    ),
                    Vec::new(),
                )
                .into();
                Some(self.complete_atomic_fact_proof_result(
                    &subset_fact,
                    proof,
                    builtin_state.verify_state(),
                )?)
            }
            _ => {
                self.try_verify_atomic_fact_as_builtin_rule_premise(&subset_fact, builtin_state)?
            }
        };
        let Some(verify_subset_result) = verify_subset_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let mut infer_result = SuccessInferResult::new();
        let stmt = in_fact.clone().into();
        infer_result.new_fact(&stmt);
        Ok((SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
            stmt,
            infer_result,
            "set_builder in power_set: param_set subset of base implies builder defines a subset of base"
                .to_string(),
            BuiltinRuleEvidence::SetBuilderInPowerSetViaParamSubset,
            vec![verify_subset_result],
        ))
        .into())
    }

    pub(super) fn verify_in_fact_list_set_in_power_set_defines_membership(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        power_set: &PowerSet,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let mut infer_result = SuccessInferResult::new();
        let premises = list_set
            .list
            .iter()
            .map(|element_box| {
                self.new_in_fact(
                    element_box.as_ref().clone(),
                    base_set.clone(),
                    in_fact.line_file.clone(),
                )
                .into()
            })
            .collect::<Vec<AtomicFact>>();
        let Some(subgoals) = self.verify_builtin_rule_premises(&premises, builtin_state)? else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let stmt = in_fact.clone().into();
        infer_result.new_fact(&stmt);
        Ok(
            (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                stmt,
                infer_result,
                "list_set in power_set: each element is in the base set".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactListSetInPowerSetDefinesMembership,
                ),
                subgoals,
            ))
            .into(),
        )
    }

    pub(super) fn verify_in_fact_by_equal_to_one_element_in_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        // Check reflexive and already-known element equalities before invoking
        // the broader equality builtin search for list-set membership.
        for (selected_index, current_element_in_list_set) in list_set.list.iter().enumerate() {
            let equality = self.new_equal_fact_from_refs(
                &in_fact.element,
                current_element_in_list_set.as_ref(),
                in_fact.line_file.clone(),
            );
            let equality_proof = self.verify_equal_fact_by_known_equality(&equality);
            let equality_atomic: AtomicFact = equality.into();
            let equal_fact_verify_result = self.complete_atomic_fact_proof_result(
                &equality_atomic,
                equality_proof,
                builtin_state.verify_state(),
            )?;
            if equal_fact_verify_result.is_success() {
                return Ok(
                    (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        BuiltinRuleEvidence::ListSetMembership(
                            ListSetMembershipBuiltinRuleEvidence { selected_index },
                        ),
                        vec![equal_fact_verify_result],
                    ))
                    .into(),
                );
            }
        }

        if list_set.list.is_empty() {
            return Ok(UnknownGenericStmtResult::new().into());
        }

        let mut left_equalities = Vec::with_capacity(list_set.list.len());
        let mut right_equalities = Vec::with_capacity(list_set.list.len());
        for listed_element in &list_set.list {
            left_equalities.push(AndChainAtomicFact::AtomicFact(
                self.new_equal_fact_from_refs(
                    &in_fact.element,
                    listed_element.as_ref(),
                    in_fact.line_file.clone(),
                )
                .into(),
            ));
            right_equalities.push(AndChainAtomicFact::AtomicFact(
                self.new_equal_fact_from_refs(
                    listed_element.as_ref(),
                    &in_fact.element,
                    in_fact.line_file.clone(),
                )
                .into(),
            ));
        }

        for branches in [left_equalities, right_equalities] {
            let premise =
                QuantifierFreeFact::OrFact(self.new_or_fact(branches, in_fact.line_file.clone()));
            let premise_result = self.try_verify_builtin_rule_premise(&premise, builtin_state)?;
            if let Some(premise_result) = premise_result {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "list-set membership from equality with one listed element".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactByEqualToOneElementInListSet),
                        vec![premise_result],
                    )
                    .into(),
                );
            }
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }

    pub(super) fn verify_not_in_fact_by_not_equal_to_every_element_in_list_set(
        &mut self,
        not_in_fact: &NotInFact,
        list_set: &ListSet,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let premises = list_set
            .list
            .iter()
            .map(|current_element| {
                self.new_not_equal_fact(
                    not_in_fact.element.clone(),
                    current_element.as_ref().clone(),
                    not_in_fact.line_file.clone(),
                )
                .into()
            })
            .collect::<Vec<AtomicFact>>();
        let Some(steps) = self.verify_builtin_rule_premises(&premises, builtin_state)? else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        Ok(
            (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                not_in_fact.clone().into(),
                format!(
                    "{} is not equal to every element in list_set {}",
                    not_in_fact.element, not_in_fact.set
                ),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyNotInFactByNotEqualToEveryElementInListSet,
                ),
                steps,
            ))
            .into(),
        )
    }

    // If object knowledge already has `element $in fn_def`, compare it to the RHS `fn ...`.
    pub fn verify_in_fact_element_in_fn_set_by_stored_definition(
        &mut self,
        element: &Obj,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Some(stored_fn_set) = self.get_cloned_object_in_fn_set(element) else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        if stored_fn_set.to_string() == expected_fn_set.to_string() {
            return Ok(
                (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "fn membership: stored fn signature matches RHS".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactElementInFnSetByStoredDefinition01,
                    ),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let flat_stored =
            SetBoundParameterGroup::collect_param_names(&stored_fn_set.set_bound_parameters);
        let flat_expected =
            SetBoundParameterGroup::collect_param_names(&expected_fn_set.body.set_bound_parameters);
        if flat_stored.len() != flat_expected.len() {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        let shared_names = self.generate_random_unused_names(flat_stored.len());
        let stored_norm =
            self.fn_set_alpha_renamed_for_display_compare(&stored_fn_set, &shared_names)?;
        let expected_norm =
            self.fn_set_alpha_renamed_for_display_compare(&expected_fn_set.body, &shared_names)?;
        if stored_norm.to_string() == expected_norm.to_string() {
            return Ok(
                (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "fn membership: stored fn signature matches RHS (alpha-renamed parameters)"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactElementInFnSetByStoredDefinition02,
                    ),
                    Vec::new(),
                ))
                .into(),
            );
        }
        Ok((UnknownGenericStmtResult::new()).into())
    }

    /// A well-defined anonymous function belongs to a function space with the
    /// same signature. Example: `fn(x E) R {f(x)} $in fn(x E) R`.
    ///
    /// This is a structural leaf. The caller owns the prior return-value
    /// well-definedness check; this comparison performs no proof search.
    pub fn verify_in_fact_anonymous_fn_signature_matches_fn_set(
        &mut self,
        anon: &AnonymousFn,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
    ) -> Result<ProveFactResult, RuntimeError> {
        let signature_from_anon = FnSet::new(
            anon.body.set_bound_parameters.clone(),
            anon.body.dom_facts.clone(),
            (*anon.body.ret_set).clone(),
        )?;
        if signature_from_anon.to_string() == expected_fn_set.to_string() {
            return Ok(
                (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature (params, dom, co-domain) matches `fn` set"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactAnonymousFnSignatureMatchesFnSet01,
                    ),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let flat_a = SetBoundParameterGroup::collect_param_names(
            &signature_from_anon.body.set_bound_parameters,
        );
        let flat_e =
            SetBoundParameterGroup::collect_param_names(&expected_fn_set.body.set_bound_parameters);
        if flat_a.len() != flat_e.len() {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        let shared_names = self.generate_random_unused_names(flat_a.len());
        let a_norm = self
            .fn_set_alpha_renamed_for_display_compare(&signature_from_anon.body, &shared_names)?;
        let e_norm =
            self.fn_set_alpha_renamed_for_display_compare(&expected_fn_set.body, &shared_names)?;
        if a_norm.to_string() == e_norm.to_string() {
            return Ok(
                (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature matches `fn` set (alpha-renamed parameters)"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactAnonymousFnSignatureMatchesFnSet02,
                    ),
                    Vec::new(),
                ))
                .into(),
            );
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }

    // Function-space membership transports across propositionally equal
    // signatures. Example: `J = A` permits `fn(x J) R {f(x)}` in `fn(x A) R`.
    pub fn verify_in_fact_anonymous_fn_signature_matches_fn_set_through_equal_sets(
        &mut self,
        anon: &AnonymousFn,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let signature_from_anon = FnSet::new(
            anon.body.set_bound_parameters.clone(),
            anon.body.dom_facts.clone(),
            (*anon.body.ret_set).clone(),
        )?;
        let signature_equality = self.verify_fn_set_with_params_equality_by_builtin_rules(
            &self.new_equal_fact(
                signature_from_anon.into(),
                expected_fn_set.clone().into(),
                in_fact.line_file.clone(),
            ),
            verify_state,
        )?;
        if signature_equality.is_success() {
            return Ok(
                (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature matches `fn` set through propositionally equal parameter sets"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactAnonymousFnSignatureMatchesFnSetThroughEqualSets),
                    Vec::new(),
                ))
                .into(),
            );
        }
        Ok((UnknownGenericStmtResult::new()).into())
    }

    pub fn verify_anonymous_fn_in_fn_set_explicit(
        &mut self,
        anon: &AnonymousFn,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(result) = self.verify_in_fact_element_in_fn_set_by_pointwise_values(
            &anon.clone().into(),
            expected_fn_set,
            in_fact,
            verify_state,
        )? {
            if result.is_success() {
                return Ok(result);
            }
        }

        let signature_result = self.verify_in_fact_anonymous_fn_signature_matches_fn_set(
            anon,
            expected_fn_set,
            in_fact,
        )?;
        if signature_result.is_success() {
            return Ok(signature_result);
        }

        self.verify_in_fact_anonymous_fn_signature_matches_fn_set_through_equal_sets(
            anon,
            expected_fn_set,
            in_fact,
            verify_state,
        )
    }

    // If every entry of `[a, b, ...]` is in `S`, then applying it at a valid index gives an element of `S`.
    // Example: `[1, 2, 3](i) $in R` follows from `i $in N+`, `i <= 3`, and each entry in `R`.
    pub(super) fn verify_in_fact_finite_seq_literal_application_in_set(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Obj::FnObj(fn_obj) = &in_fact.element else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let FnObjHead::FiniteSeqListObj(list) = fn_obj.head.as_ref() else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        let index_obj = fn_obj.body[0][0].as_ref().clone();
        let index_in_n_pos: AtomicFact = self
            .new_in_fact(
                index_obj.clone(),
                StandardSet::NPos.into(),
                in_fact.line_file.clone(),
            )
            .into();
        let list_len_obj: Obj = Number::new(list.objs.len().to_string()).into();
        let index_in_range: AtomicFact = self
            .new_less_equal_fact(index_obj, list_len_obj, in_fact.line_file.clone())
            .into();
        let mut premises = vec![index_in_n_pos, index_in_range];
        for element in list.objs.iter() {
            premises.push(
                self.new_in_fact(
                    element.as_ref().clone(),
                    target_set_obj.clone(),
                    in_fact.line_file.clone(),
                )
                .into(),
            );
        }
        let Some(step_results) = self.verify_builtin_rule_premises(&premises, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        Ok(
            (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                format!(
                    "finite sequence literal application is in {}",
                    target_set_obj
                ),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactFiniteSeqLiteralApplicationInSet,
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
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Obj::StandardSet(_) = target_set_obj else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Obj::ObjAtIndex(obj_at_index) = &in_fact.element else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(cart) = self.get_object_equal_to_cart(obj_at_index.obj.as_ref()) else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(index_number) = self.resolve_obj_to_number(&obj_at_index.index) else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Ok(one_based_index) = index_number.normalized_value.parse::<usize>() else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        if one_based_index == 0 || one_based_index > cart.args.len() {
            return Ok((UnknownGenericStmtResult::new()).into());
        }

        let factor = cart.args[one_based_index - 1].as_ref();
        let Obj::ListSet(list_set) = factor else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        let premises = list_set
            .list
            .iter()
            .map(|element| {
                self.new_in_fact(
                    element.as_ref().clone(),
                    target_set_obj.clone(),
                    in_fact.line_file.clone(),
                )
                .into()
            })
            .collect::<Vec<AtomicFact>>();
        let Some(step_results) = self.verify_builtin_rule_premises(&premises, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        Ok(
            (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                format!(
                    "cart projection list_set elements are all in {}",
                    target_set_obj
                ),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactObjAtIndexInStandardSetByCartFactorListSet,
                ),
                step_results,
            ))
            .into(),
        )
    }

    pub(super) fn verify_in_fact_by_standard_subset_membership(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Obj::StandardSet(target_set) = &in_fact.set else {
            return Ok(UnknownGenericStmtResult::new().into());
        };

        // Membership is monotone through the standard numeric-set hierarchy.
        // Derive candidates from the target, not from materialized owner-set
        // history. Example: a cold `(x, y)[1] $in C` query may prove the
        // projection is in `N`, then widen that result to `C`.
        for source_set in target_set.proper_subsets_in_membership_proof_order() {
            let source_set_obj: Obj = source_set.into();
            let source_membership: AtomicFact = self
                .new_in_fact(
                    in_fact.element.clone(),
                    source_set_obj.clone(),
                    in_fact.line_file.clone(),
                )
                .into();
            let source_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &source_membership,
                builtin_state,
            )?;
            if let Some(source_result) = source_result {
                return Ok(
                    (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, source_set_obj, in_fact.set
                        ),
                        BuiltinRuleEvidence::StandardSetMembershipProjection,
                        vec![source_result],
                    ))
                    .into(),
                );
            }
        }
        Ok((UnknownGenericStmtResult::new()).into())
    }

    /// A member of a numeric list set inherits a standard numeric carrier
    /// shared by every listed value. Example: `x {1, 2}` implies `x $in R`.
    pub(super) fn verify_in_fact_by_known_list_set_carrier(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Obj::StandardSet(target_set) = &in_fact.set else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        for source_set in self.known_sets_containing_obj(&in_fact.element) {
            let Obj::ListSet(list_set) = &source_set else {
                continue;
            };
            let source_membership: AtomicFact = self
                .new_in_fact(
                    in_fact.element.clone(),
                    source_set.clone(),
                    in_fact.line_file.clone(),
                )
                .into();
            let Some(source_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &source_membership,
                builtin_state,
            )?
            else {
                continue;
            };

            let mut steps = vec![source_result];
            let mut all_elements_match = true;
            for element in &list_set.list {
                let element_membership: AtomicFact = self
                    .new_in_fact(
                        element.as_ref().clone(),
                        in_fact.set.clone(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                let Some(evaluated_number) = element.evaluate_to_normalized_decimal_number() else {
                    all_elements_match = false;
                    break;
                };
                let AtomicFact::InFact(element_in_fact) = &element_membership else {
                    unreachable!("constructed an in-fact")
                };
                let result = builtin_in_fact_result_for_evaluated_number_in_standard_set(
                    element_in_fact,
                    &evaluated_number,
                    target_set,
                );
                if !result.is_success() {
                    all_elements_match = false;
                    break;
                }
                steps.push(self.complete_atomic_fact_proof_result(
                    &element_membership,
                    result,
                    builtin_state.verify_state(),
                )?);
            }
            if all_elements_match {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "listed-set member inherits a carrier shared by every listed element"
                            .to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactByKnownListSetCarrier),
                        steps,
                    )
                    .into(),
                );
            }
        }
        Ok((UnknownGenericStmtResult::new()).into())
    }

    pub(super) fn verify_not_in_z_for_resolved_numeric_div(
        &self,
        not_in_fact: &NotInFact,
    ) -> Option<ProveFactResult> {
        let (numerator, denominator) = self.resolved_numeric_div_operands(&not_in_fact.element)?;
        if !number_is_in_z(&numerator) || !number_is_in_z_star(&denominator) {
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

        let obj_key = obj_equality_key(obj);
        for env in self.iter_environments_from_top() {
            let Some((_, equal_objs)) = env.facts.known_equality.get(&obj_key) else {
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
