use super::*;
use std::rc::Rc;

impl Runtime {
    fn unfold_set_builder_definition_without_transport_reentry(
        &mut self,
        obj: &Obj,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<Obj>, RuntimeError> {
        if self.active_set_builder_forall_transport
            || self.known_equality_candidate_replay_depth != 0
        {
            return Ok(None);
        }
        self.active_set_builder_forall_transport = true;
        let result = self
            .unfold_known_fn_application_to_set_builder(obj, verify_state)
            .map(|set_builder| set_builder.map(Obj::from));
        self.active_set_builder_forall_transport = false;
        result
    }

    pub(crate) fn try_verify_set_builder_membership_definition_transport(
        &mut self,
        goal: &InFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::SetBuilder(goal_builder) = &goal.set else {
            return Ok(None);
        };
        let memberships: Vec<InFact> = self
            .iter_environments_from_top()
            .flat_map(|environment| environment.known_owner_sets.values())
            .flat_map(|owner_sets| owner_sets.values())
            .filter(|membership| {
                verify_equality_by_they_are_the_same(&membership.element, &goal.element)
            })
            .cloned()
            .collect();
        let final_state = UseContextVerifyState::new_with_final_round(true);

        for membership in memberships {
            let unfolded = match &membership.set {
                Obj::SetBuilder(set_builder) => Some(set_builder.clone()),
                _ => match self.unfold_set_builder_definition_without_transport_reentry(
                    &membership.set,
                    &final_state,
                )? {
                    Some(Obj::SetBuilder(set_builder)) => Some(set_builder),
                    _ => self.get_obj_equal_to_set_builder(&membership.set),
                },
            };
            let Some(unfolded) = unfolded else {
                continue;
            };
            let unfolded_obj: Obj = unfolded.into();
            let goal_obj: Obj = goal_builder.clone().into();
            if !objs_equal_with_nested_binder_alpha_equivalence(&unfolded_obj, &goal_obj) {
                continue;
            }

            let membership_result = Self::stmt_result_for_indexed_fact(
                membership.clone().into(),
                "known membership in an equal one-layer set-builder definition",
            );
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    goal.clone().into(),
                    "set-builder membership transport through one unfolded definition".to_string(),
                    vec![membership_result],
                )
                .into(),
            ));
        }

        if self.active_set_builder_forall_transport
            || self.known_equality_candidate_replay_depth != 0
        {
            return Ok(None);
        }
        let forall_memberships: Vec<(InFact, Rc<KnownForallFactParamsAndDom>)> = self
            .iter_environments_from_top()
            .flat_map(|environment| {
                environment
                    .known_atomic_facts_in_forall_facts
                    .values()
                    .flat_map(|facts| facts.iter())
                    .chain(
                        environment
                            .known_atomic_facts_in_forall_facts_by_arg_shape
                            .values()
                            .flat_map(|shape_map| shape_map.values())
                            .flat_map(|facts| facts.iter()),
                    )
            })
            .filter_map(|(fact, params)| match fact {
                AtomicFact::InFact(member) => Some((member.clone(), params.clone())),
                _ => None,
            })
            .collect();
        let zero: Obj = Number::new("0".to_string()).into();
        for (membership_pattern, forall_context) in forall_memberships {
            let pattern_match: AtomicFact = EqualFact::new(
                membership_pattern.element.clone(),
                zero.clone(),
                goal.line_file.clone(),
            )
            .into();
            let goal_match: AtomicFact =
                EqualFact::new(goal.element.clone(), zero.clone(), goal.line_file.clone()).into();
            let arg_map = self.match_atomic_fact_args_against_known_forall_ordered_args(
                &pattern_match,
                &goal_match,
                &forall_context.params_def,
            )?;
            let Some(arg_map) = arg_map else {
                continue;
            };
            let membership_pattern_atomic: AtomicFact = membership_pattern.clone().into();
            let instantiated = self.inst_atomic_fact(
                &membership_pattern_atomic,
                &arg_map,
                ParamObjType::Forall,
                Some(&goal.line_file),
            )?;
            let AtomicFact::InFact(instantiated_membership) = &instantiated else {
                unreachable!()
            };
            let unfolded = self.unfold_set_builder_definition_without_transport_reentry(
                &instantiated_membership.set,
                &final_state,
            )?;
            let instantiated_builder = match unfolded {
                Some(Obj::SetBuilder(set_builder)) => Some(set_builder),
                _ => self.get_obj_equal_to_set_builder(&instantiated_membership.set),
            };
            let Some(instantiated_builder) = instantiated_builder else {
                continue;
            };
            let instantiated_builder_obj: Obj = instantiated_builder.into();
            let goal_builder_obj: Obj = goal_builder.clone().into();
            if !objs_equal_with_nested_binder_alpha_equivalence(
                &instantiated_builder_obj,
                &goal_builder_obj,
            ) {
                continue;
            }
            let requirement_state = UseContextVerifyState::new_with_final_round(true)
                .without_known_forall_for_equality();
            self.active_set_builder_forall_transport = true;
            let membership_result = self.verify_args_satisfy_forall_requirements(
                &membership_pattern_atomic,
                &forall_context,
                arg_map,
                &instantiated,
                &requirement_state,
            );
            self.active_set_builder_forall_transport = false;
            let Some(membership_success) = membership_result? else {
                continue;
            };
            let membership_result: StmtResult = membership_success.into();
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    goal.clone().into(),
                    "set-builder membership transport from a known universal named-set membership"
                        .to_string(),
                    vec![membership_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    pub(crate) fn try_verify_atomic_fact_from_known_set_builder_membership(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if self.known_equality_candidate_replay_depth == 0
            && !matches!(goal, AtomicFact::InFact(_))
            && !self.active_set_builder_forall_transport
        {
            let forall_memberships: Vec<(InFact, Rc<KnownForallFactParamsAndDom>)> = self
                .iter_environments_from_top()
                .flat_map(|environment| {
                    environment
                        .known_atomic_facts_in_forall_facts
                        .values()
                        .flat_map(|facts| facts.iter())
                        .chain(
                            environment
                                .known_atomic_facts_in_forall_facts_by_arg_shape
                                .values()
                                .flat_map(|shape_map| shape_map.values())
                                .flat_map(|facts| facts.iter()),
                        )
                })
                .filter_map(|(fact, params)| match fact {
                    AtomicFact::InFact(member) => Some((member.clone(), params.clone())),
                    _ => None,
                })
                .collect();
            for (membership_pattern, forall_context) in forall_memberships {
                let set_builder = match &membership_pattern.set {
                    Obj::SetBuilder(set_builder) => Some(set_builder.clone()),
                    _ => match self.unfold_set_builder_definition_without_transport_reentry(
                        &membership_pattern.set,
                        &UseContextVerifyState::new_with_final_round(true),
                    )? {
                        Some(Obj::SetBuilder(set_builder)) => Some(set_builder),
                        _ => None,
                    },
                };
                let Some(set_builder) = set_builder else {
                    continue;
                };
                let mut element_substitution = std::collections::HashMap::new();
                insert_symbol_substitution(
                    &mut element_substitution,
                    &set_builder.param_binding,
                    membership_pattern.element.clone(),
                );
                for defining_fact in &set_builder.facts {
                    let instantiated_pattern = self.inst_quantifier_free_fact(
                        defining_fact,
                        &element_substitution,
                        ParamObjType::SetBuilder,
                        Some(&goal.line_file()),
                    )?;
                    let QuantifierFreeFact::AtomicFact(atomic_pattern) = instantiated_pattern
                    else {
                        continue;
                    };
                    let Some(arg_map) = self
                        .match_atomic_fact_args_against_known_forall_ordered_args(
                            &atomic_pattern,
                            goal,
                            &forall_context.params_def,
                        )?
                    else {
                        continue;
                    };
                    let membership_pattern_atomic: AtomicFact = membership_pattern.clone().into();
                    let instantiated_membership = self.inst_atomic_fact(
                        &membership_pattern_atomic,
                        &arg_map,
                        ParamObjType::Forall,
                        Some(&goal.line_file()),
                    )?;
                    let requirement_state = UseContextVerifyState::new_with_final_round(true)
                        .without_known_forall_for_equality();
                    self.active_set_builder_forall_transport = true;
                    let membership_result = self.verify_args_satisfy_forall_requirements(
                        &membership_pattern_atomic,
                        &forall_context,
                        arg_map,
                        &instantiated_membership,
                        &requirement_state,
                    );
                    self.active_set_builder_forall_transport = false;
                    let Some(membership_success) = membership_result? else {
                        continue;
                    };
                    let membership_result: StmtResult = membership_success.into();
                    return Ok(Some(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            goal.clone().into(),
                            "universal set-builder membership eliminates to its defining fact"
                                .to_string(),
                            vec![membership_result],
                        )
                        .into(),
                    ));
                }
            }
        }
        let mut memberships: Vec<InFact> = self
            .iter_environments_from_top()
            .flat_map(|environment| {
                environment
                    .known_atomic_facts_with_2_args
                    .values()
                    .flat_map(|facts| facts.values())
            })
            .filter_map(|fact| match fact {
                AtomicFact::InFact(member) => Some(member.clone()),
                _ => None,
            })
            .collect();
        for environment in self.iter_environments_from_top() {
            for owner_sets in environment.known_owner_sets.values() {
                for membership in owner_sets.values() {
                    if !memberships
                        .iter()
                        .any(|known| known.to_string() == membership.to_string())
                    {
                        memberships.push(membership.clone());
                    }
                }
            }
        }
        let final_state = UseContextVerifyState::new_with_final_round(false);

        for membership in memberships {
            let set_builder = match &membership.set {
                Obj::SetBuilder(set_builder) => Some(set_builder.clone()),
                _ => match self.unfold_set_builder_definition_without_transport_reentry(
                    &membership.set,
                    &final_state,
                )? {
                    Some(Obj::SetBuilder(set_builder)) => Some(set_builder),
                    _ => self.get_obj_equal_to_set_builder(&membership.set),
                },
            };
            let Some(set_builder) = set_builder else {
                continue;
            };

            let mut substitutions = std::collections::HashMap::new();
            insert_symbol_substitution(
                &mut substitutions,
                &set_builder.param_binding,
                membership.element.clone(),
            );
            for defining_fact in &set_builder.facts {
                let instantiated = self.inst_quantifier_free_fact(
                    defining_fact,
                    &substitutions,
                    ParamObjType::SetBuilder,
                    Some(&goal.line_file()),
                )?;
                let QuantifierFreeFact::AtomicFact(instantiated_atomic) = instantiated else {
                    continue;
                };
                if instantiated_atomic.to_string() != goal.to_string() {
                    continue;
                }

                let membership_atomic: AtomicFact = membership.clone().into();
                let membership_result = Self::stmt_result_for_indexed_fact(
                    membership_atomic,
                    "known membership in a set-builder or its one-layer named definition",
                );
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        goal.clone().into(),
                        "set-builder membership eliminates to its instantiated defining fact"
                            .to_string(),
                        vec![membership_result],
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // Binary-union introduction: a member of either side is in the union.
    // Example: `x $in A` proves `x $in union(A, B)`.
    pub(super) fn verify_in_fact_in_union_by_member_of_either_side(
        &mut self,
        in_fact: &InFact,
        union: &Union,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        for (side, side_name) in [
            (union.left.as_ref(), "left"),
            (union.right.as_ref(), "right"),
        ] {
            let member_fact: AtomicFact = InFact::new(
                in_fact.element.clone(),
                side.clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let member_result = self.verify_builtin_rule_premise(&member_fact, builtin_state)?;
            if member_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        format!("union membership: member of the {side_name} side"),
                        BuiltinRuleEvidence::Set(if side_name == "left" {
                            SetBuiltinRule::UnionMembershipLeft
                        } else {
                            SetBuiltinRule::UnionMembershipRight
                        }),
                        vec![member_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    // Binary-intersection introduction: a member of both sides is in the intersection.
    // Example: `x $in A`, `x $in B` prove `x $in intersect(A, B)`.
    pub(super) fn verify_in_fact_in_intersect_by_member_of_both_sides(
        &mut self,
        in_fact: &InFact,
        intersect: &Intersect,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_member_fact: AtomicFact = InFact::new(
            in_fact.element.clone(),
            intersect.left.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let left_member_result =
            self.verify_builtin_rule_premise(&left_member_fact, builtin_state)?;
        if !left_member_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let right_member_fact: AtomicFact = InFact::new(
            in_fact.element.clone(),
            intersect.right.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let right_member_result =
            self.verify_builtin_rule_premise(&right_member_fact, builtin_state)?;
        if !right_member_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "intersection membership: member of both sides".to_string(),
                BuiltinRuleEvidence::Set(SetBuiltinRule::IntersectMembershipBoth),
                vec![left_member_result, right_member_result],
            )
            .into(),
        )
    }

    // A non-member of either side is outside the intersection.
    // Example: `not x $in A` proves `not x $in intersect(A, B)`.
    pub(super) fn verify_not_in_fact_not_in_intersect_by_non_member_of_either_side(
        &mut self,
        not_in_fact: &NotInFact,
        intersect: &Intersect,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        for (side, side_name) in [
            (intersect.left.as_ref(), "left"),
            (intersect.right.as_ref(), "right"),
        ] {
            let non_member_fact: AtomicFact = NotInFact::new(
                not_in_fact.element.clone(),
                side.clone(),
                not_in_fact.line_file.clone(),
            )
            .into();
            let non_member_result =
                self.verify_builtin_rule_premise(&non_member_fact, builtin_state)?;
            if non_member_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        not_in_fact.clone().into(),
                        format!("intersection non-membership: non-member of the {side_name} side"),
                        BuiltinRuleEvidence::Set(if side_name == "left" {
                            SetBuiltinRule::IntersectNonMembershipLeft
                        } else {
                            SetBuiltinRule::IntersectNonMembershipRight
                        }),
                        vec![non_member_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    // Set-difference introduction: a left member excluded from the right side is in the difference.
    // Example: `x $in A`, `not x $in B` prove `x $in set_minus(A, B)`.
    pub(super) fn verify_in_fact_in_set_minus_by_member_and_non_member(
        &mut self,
        in_fact: &InFact,
        set_minus: &SetMinus,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_member_fact: AtomicFact = InFact::new(
            in_fact.element.clone(),
            set_minus.left.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let left_member_result =
            self.verify_builtin_rule_premise(&left_member_fact, builtin_state)?;
        if !left_member_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let right_non_member_fact: AtomicFact = NotInFact::new(
            in_fact.element.clone(),
            set_minus.right.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let right_non_member_result =
            self.verify_builtin_rule_premise(&right_non_member_fact, builtin_state)?;
        if !right_non_member_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "set-minus membership: member of left side and non-member of right side"
                    .to_string(),
                BuiltinRuleEvidence::Set(SetBuiltinRule::SetMinusMembership),
                vec![left_member_result, right_non_member_result],
            )
            .into(),
        )
    }

    // Family-union introduction: `x $in big_union(F)` follows from a member set
    // containing `x`, either as a known existential or as concrete facts.
    // Example: `A $in F` and `x $in A` prove `x $in big_union(F)`.
    pub(super) fn verify_in_fact_in_big_union_by_member_witness(
        &mut self,
        in_fact: &InFact,
        big_union: &BigUnion,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact = self.big_union_membership_exist_fact(in_fact, big_union)?;
        let exist_result =
            self.verify_exist_fact_with_known_exist_fact(&exist_fact, &exist_fact)?;
        if exist_result.is_true() {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "big_union membership: an element of a member set is in the family union"
                        .to_string(),
                    vec![exist_result],
                )
                .into(),
            );
        }

        for member_set in
            self.known_member_sets_for_big_union_family(in_fact, big_union.left.as_ref())
        {
            let member_set_in_family: AtomicFact = InFact::new(
                member_set.clone(),
                big_union.left.as_ref().clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let member_set_result =
                self.verify_builtin_rule_premise(&member_set_in_family, builtin_state)?;
            if !member_set_result.is_true() {
                continue;
            }

            let element_in_member_set: AtomicFact = InFact::new(
                in_fact.element.clone(),
                member_set,
                in_fact.line_file.clone(),
            )
            .into();
            let element_result =
                self.verify_builtin_rule_premise(&element_in_member_set, builtin_state)?;
            if element_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        "big_union membership: an element of a member set is in the family union"
                            .to_string(),
                        vec![member_set_result, element_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn big_union_membership_exist_fact(
        &self,
        in_fact: &InFact,
        big_union: &BigUnion,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let member_name = self.generate_internal_binder_name();
        let member_group = self.fresh_param_group_with_type(
            vec![member_name],
            ParamType::Obj(big_union.left.as_ref().clone()),
        )?;
        let member_obj = obj_for_bound_param_in_scope(&member_group.params[0], ParamObjType::Exist);
        let element_in_member: AtomicFact = InFact::new(
            in_fact.element.clone(),
            member_obj,
            in_fact.line_file.clone(),
        )
        .into();
        let exist_body = ExistentialSpec::new(
            ParamDefWithType::new(vec![member_group]),
            vec![element_in_member.into()],
            in_fact.line_file.clone(),
        )?;
        Ok(ExistFactEnum::ExistFact(exist_body))
    }

    // Replacement introduction: `z $in replacement(P, A)` follows from a
    // relation witness in the source set.
    // Example: `x $in A` and `$P(x, z)` prove `z $in replacement(P, A)`.
    pub(super) fn verify_in_fact_in_replacement_by_relation_witness(
        &mut self,
        in_fact: &InFact,
        replacement: &Replacement,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact = self.replacement_membership_exist_fact(in_fact, replacement)?;
        let exist_result =
            self.verify_exist_fact_with_known_exist_fact(&exist_fact, &exist_fact)?;
        if exist_result.is_true() {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "replacement membership: a relation witness is in the replacement set"
                        .to_string(),
                    vec![exist_result],
                )
                .into(),
            );
        }

        for preimage in self.known_preimages_for_replacement_target(in_fact, replacement) {
            let preimage_in_source: AtomicFact = InFact::new(
                preimage.clone(),
                replacement.source_set.as_ref().clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let mut preimage_result =
                self.verify_builtin_rule_premise(&preimage_in_source, builtin_state)?;
            // Literal source membership is a bounded structural leaf, so it
            // may discharge the witness carrier without consuming a second
            // recursive builtin-rule layer. Example: `$P(1,z)` introduces
            // `z $in replacement(P,{1,2})`.
            if !preimage_result.is_true() {
                if let (AtomicFact::InFact(preimage_in_fact), Obj::ListSet(source_elements)) =
                    (&preimage_in_source, replacement.source_set.as_ref())
                {
                    preimage_result = self.verify_in_fact_by_equal_to_one_element_in_list_set(
                        preimage_in_fact,
                        source_elements,
                        builtin_state,
                    )?;
                }
            }
            if !preimage_result.is_true() {
                continue;
            }

            let relation_fact: AtomicFact = NormalAtomicFact::new(
                replacement.prop_name.clone(),
                vec![preimage, in_fact.element.clone()],
                in_fact.line_file.clone(),
            )
            .into();
            let relation_result =
                self.verify_builtin_rule_premise(&relation_fact, builtin_state)?;
            if relation_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        "replacement membership: a relation witness is in the replacement set"
                            .to_string(),
                        vec![preimage_result, relation_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn replacement_membership_exist_fact(
        &self,
        in_fact: &InFact,
        replacement: &Replacement,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let preimage_name = self.generate_internal_binder_name();
        let preimage_group = self.fresh_param_group_with_type(
            vec![preimage_name],
            ParamType::Obj(replacement.source_set.as_ref().clone()),
        )?;
        let preimage_obj =
            obj_for_bound_param_in_scope(&preimage_group.params[0], ParamObjType::Exist);
        let relation_fact: AtomicFact = NormalAtomicFact::new(
            replacement.prop_name.clone(),
            vec![preimage_obj, in_fact.element.clone()],
            in_fact.line_file.clone(),
        )
        .into();
        let exist_body = ExistentialSpec::new(
            ParamDefWithType::new(vec![preimage_group]),
            vec![relation_fact.into()],
            in_fact.line_file.clone(),
        )?;
        Ok(ExistFactEnum::ExistFact(exist_body))
    }

    pub(super) fn known_preimages_for_replacement_target(
        &self,
        in_fact: &InFact,
        replacement: &Replacement,
    ) -> Vec<Obj> {
        let atomic_fact: AtomicFact = in_fact.clone().into();
        let module_names = self.atomic_fact_referenced_module_names(&atomic_fact);
        let target_keys =
            self.all_objs_equal_to_arg_for_known_atomic_fact(&in_fact.element, &module_names);
        let lookup_key = (replacement.prop_name.to_string(), true);
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            Self::extend_known_preimages_for_replacement_target_from_environment(
                environment,
                &lookup_key,
                &target_keys,
                &mut candidates,
            );
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                Self::extend_known_preimages_for_replacement_target_from_environment(
                    environment,
                    &lookup_key,
                    &target_keys,
                    &mut candidates,
                );
            }
        }

        let mut seen = Vec::new();
        candidates.retain(|candidate: &Obj| {
            let key = candidate.to_string();
            if seen.contains(&key) {
                return false;
            }
            seen.push(key);
            true
        });
        candidates
    }

    pub(super) fn extend_known_preimages_for_replacement_target_from_environment(
        environment: &Environment,
        lookup_key: &(String, bool),
        target_keys: &[String],
        candidates: &mut Vec<Obj>,
    ) {
        let Some(known_relation_facts) = environment.known_atomic_facts_with_2_args.get(lookup_key)
        else {
            return;
        };
        for ((_, known_target_key), known_fact) in known_relation_facts.iter() {
            if !target_keys.contains(known_target_key) {
                continue;
            }
            let AtomicFact::NormalAtomicFact(known_relation) = known_fact else {
                continue;
            };
            let Some(preimage) = known_relation.body.first() else {
                continue;
            };
            candidates.push(preimage.clone());
        }
    }

    pub(super) fn known_member_sets_for_big_union_family(
        &self,
        in_fact: &InFact,
        family: &Obj,
    ) -> Vec<Obj> {
        let atomic_fact: AtomicFact = in_fact.clone().into();
        let module_names = self.atomic_fact_referenced_module_names(&atomic_fact);
        let family_keys = self.all_objs_equal_to_arg_for_known_atomic_fact(family, &module_names);
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            Self::extend_known_member_sets_for_big_union_family_from_environment(
                environment,
                &family_keys,
                &mut candidates,
            );
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                Self::extend_known_member_sets_for_big_union_family_from_environment(
                    environment,
                    &family_keys,
                    &mut candidates,
                );
            }
        }

        let mut seen = Vec::new();
        candidates.retain(|candidate: &Obj| {
            let key = candidate.to_string();
            if seen.contains(&key) {
                return false;
            }
            seen.push(key);
            true
        });
        candidates
    }

    pub(super) fn extend_known_member_sets_for_big_union_family_from_environment(
        environment: &Environment,
        family_keys: &[String],
        candidates: &mut Vec<Obj>,
    ) {
        let lookup_key = (IN.to_string(), true);
        let Some(known_membership_facts) =
            environment.known_atomic_facts_with_2_args.get(&lookup_key)
        else {
            return;
        };
        for ((_, known_family_key), known_fact) in known_membership_facts.iter() {
            if !family_keys.contains(known_family_key) {
                continue;
            }
            let AtomicFact::InFact(known_in_fact) = known_fact else {
                continue;
            };
            candidates.push(known_in_fact.element.clone());
        }
    }

    // Function range introduction: if `f(a)` is well-defined, then it is in `fn_range(f)`.
    // Example: `have f fn(x R: x > 0) R`, `1 > 0` proves `f(1) $in fn_range(f)`.
    pub(super) fn verify_in_fact_fn_application_in_fn_range(
        &mut self,
        in_fact: &InFact,
        fn_obj: &FnObj,
        fn_range: &FnRange,
    ) -> Result<StmtResult, RuntimeError> {
        let head_obj: Obj = fn_obj.head.as_ref().clone().into();
        if !objs_equal_with_nested_binder_alpha_equivalence(&head_obj, &fn_range.function) {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        if fn_obj.body.len() != 1
            || fn_obj.body[0].len() != body.params_def_with_set.number_of_params()
        {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range membership: a well-defined function application is in the function range"
                    .to_string(),
                Vec::new(),
            )
            .into(),
        )
    }

    // The range of `f : ... -> T` is a subset of `T`; hence it is in `power_set(U)` when `T subset U`.
    // Example: `have f fn(x S) T` proves `fn_range(f) $in power_set(T)`.
    pub(super) fn verify_in_fact_fn_range_in_power_set(
        &mut self,
        in_fact: &InFact,
        fn_range: &FnRange,
        power_set: &PowerSet,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        let subset_fact: AtomicFact = SubsetFact::new(
            body.ret_set.as_ref().clone(),
            power_set.set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let mut subset_result = self.verify_builtin_rule_premise(&subset_fact, builtin_state)?;
        if !subset_result.is_true()
            && (objs_equal_with_nested_binder_alpha_equivalence(
                body.ret_set.as_ref(),
                power_set.set.as_ref(),
            ) || matches!(
                (body.ret_set.as_ref(), power_set.set.as_ref()),
                (Obj::StandardSet(left), Obj::StandardSet(right))
                    if left.is_subset_eq(right)
            ))
        {
            subset_result = FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                subset_fact.clone().into(),
                "structural subset".to_string(),
                Vec::new(),
            )
            .into();
        }
        if !subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range power_set membership: function range is contained in the codomain"
                    .to_string(),
                vec![subset_result],
            )
            .into(),
        )
    }

    // Proves power-set membership from the subset definition.
    // Example: if `A $subset B`, then `A $in power_set(B)`.
    pub(super) fn verify_in_fact_in_power_set_via_subset(
        &mut self,
        in_fact: &InFact,
        power_set: &PowerSet,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let subset_fact: AtomicFact = SubsetFact::new(
            in_fact.element.clone(),
            power_set.set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let mut subset_result = self.verify_builtin_rule_premise(&subset_fact, builtin_state)?;
        if !subset_result.is_true()
            && (objs_equal_with_nested_binder_alpha_equivalence(
                &in_fact.element,
                power_set.set.as_ref(),
            ) || matches!(
                (&in_fact.element, power_set.set.as_ref()),
                (Obj::StandardSet(left), Obj::StandardSet(right))
                    if left.is_subset_eq(right)
            ))
        {
            subset_result = FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                subset_fact.clone().into(),
                "structural subset".to_string(),
                Vec::new(),
            )
            .into();
        }
        if !subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "power_set membership: a subset of the base set is an element of the power set"
                    .to_string(),
                vec![subset_result],
            )
            .into(),
        )
    }

    // General Cartesian product membership: a member is a function on `I` into `big_union(s)`
    // satisfying the named pointwise choice-function property.
    // Example: `f $in general_cart(I, s, g)` follows from
    // `f $in fn(t I)big_union(s)` and `$is_choice_function_for(I, s, g, f)`.
    pub(crate) fn verify_in_fact_in_general_cart_by_defining_facts(
        &mut self,
        in_fact: &InFact,
        general_cart: &GeneralCart,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_fact: AtomicFact = InFact::new(
            in_fact.element.clone(),
            general_cart_member_fn_set(self, general_cart)?,
            in_fact.line_file.clone(),
        )
        .into();
        let fn_set_result = self.verify_atomic_fact(&fn_set_fact, verify_state)?;
        if !fn_set_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let choice_fact = general_cart_member_choice_fact(
            general_cart,
            in_fact.element.clone(),
            in_fact.line_file.clone(),
        );
        let choice_result = self.verify_atomic_fact(&choice_fact, verify_state)?;
        if !choice_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "general_cart membership: function carrier and named pointwise choice property"
                    .to_string(),
                vec![fn_set_result, choice_result],
            )
            .into(),
        )
    }

    pub(crate) fn verify_in_fact_in_set_builder_by_defining_facts(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let mut step_results = Vec::with_capacity(set_builder.facts.len() + 1);

        let element_in_param_set: AtomicFact = InFact::new(
            in_fact.element.clone(),
            *set_builder.param_set.clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let element_in_param_set_result =
            self.verify_atomic_fact(&element_in_param_set, verify_state)?;
        if !element_in_param_set_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(element_in_param_set_result);

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        insert_symbol_substitution(
            &mut param_to_arg_map,
            &set_builder.param_binding,
            in_fact.element.clone(),
        );

        for fact_in_set_builder in set_builder.facts.iter() {
            let instantiated_fact = self
                .inst_quantifier_free_fact(
                    fact_in_set_builder,
                    &param_to_arg_map,
                    ParamObjType::SetBuilder,
                    Some(&in_fact.line_file),
                )
                .map_err(|e| {
                    let fact: Fact = in_fact.clone().into();
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(fact.into_stmt()),
                        format!(
                            "failed to instantiate set builder fact while verifying `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    )))
                })?;

            let instantiated_fact_result =
                self.verify_fact_full(&instantiated_fact.to_fact(), verify_state)?;
            if !instantiated_fact_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(instantiated_fact_result);
        }

        Ok(FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "set builder membership: element is in the base set and satisfies all defining facts"
                .to_string(),
            step_results,
        )
        .into())
    }

    // Membership through a set-valued definition: if `S(a) = {x T: P(x)}`,
    // then `y $in S(a)` is checked by unfolding one layer and proving
    // `y $in T` plus `P(y)`. This includes instantiated template definitions.
    // Examples: `(3, 4) $in circle(5)` and `y $in \selected<T>`.
    pub(crate) fn maybe_verify_in_fact_in_unfolded_user_defined_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let goal_key = in_fact.to_string();
        if !self
            .active_set_builder_membership_unfolds
            .insert(goal_key.clone())
        {
            return Ok(None);
        }
        let result =
            self.maybe_verify_in_fact_in_unfolded_user_defined_set_once(in_fact, verify_state);
        self.active_set_builder_membership_unfolds.remove(&goal_key);
        result
    }

    fn maybe_verify_in_fact_in_unfolded_user_defined_set_once(
        &mut self,
        in_fact: &InFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::InstantiatedTemplateObj(template_obj) = &in_fact.set {
            self.materialize_instantiated_template_obj(template_obj, verify_state)?;
        }
        let set_builder = self
            .unfold_known_fn_application_to_set_builder(&in_fact.set, verify_state)?
            .or_else(|| self.get_obj_equal_to_set_builder(&in_fact.set));
        let Some(set_builder) = set_builder else {
            return Ok(None);
        };

        let unfolded_fact = InFact::new(
            in_fact.element.clone(),
            set_builder.clone().into(),
            in_fact.line_file.clone(),
        );
        let unfolded_result = self.verify_in_fact_in_set_builder_by_defining_facts(
            &unfolded_fact,
            &set_builder,
            verify_state,
        )?;
        if !unfolded_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "membership in a set-valued definition: unfold one function or template definition to a set builder".to_string(),
                vec![unfolded_result],
            )
            .into(),
        ))
    }

    pub(crate) fn verify_in_fact_by_struct_obj(
        &mut self,
        in_fact: &InFact,
        struct_obj: &StructObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &Obj::StructObj(struct_obj.clone()),
            verify_state,
        )?;
        let (def, header_map) = self.struct_header_param_to_arg_map(struct_obj, verify_state)?;
        let field_types = self.instantiated_struct_field_types(struct_obj, verify_state)?;
        let carrier_obj = self.struct_carrier_from_field_types(field_types.clone());
        let carrier_membership: AtomicFact = InFact::new(
            in_fact.element.clone(),
            carrier_obj,
            in_fact.line_file.clone(),
        )
        .into();
        let carrier_result = if field_types.len() == 1 {
            self.verify_atomic_fact(&carrier_membership, verify_state)?
        } else if let Obj::Tuple(tuple) = &in_fact.element {
            if tuple.args.len() != def.fields.len() {
                return Ok((StmtUnknown::new()).into());
            }
            let mut field_results = Vec::with_capacity(tuple.args.len());
            for (field_value, field_type) in tuple.args.iter().zip(field_types.iter()) {
                let field_result = self.verify_obj_satisfies_param_type(
                    field_value.as_ref().clone(),
                    &ParamType::Obj(field_type.clone()),
                    verify_state,
                )?;
                if !field_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                field_results.push(field_result);
            }
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                carrier_membership.into(),
                "dependent struct constructor: each literal tuple field has its instantiated carrier"
                    .to_string(),
                field_results,
            )
            .into()
        } else {
            self.verify_atomic_fact(&carrier_membership, verify_state)?
        };
        if !carrier_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let mut step_results = vec![carrier_result];
        let mut field_map = HashMap::new();
        for (index, field) in def.fields.iter().enumerate() {
            let field_obj = if def.fields.len() == 1 {
                in_fact.element.clone()
            } else {
                match &in_fact.element {
                    Obj::Tuple(tuple) => (*tuple.args[index]).clone(),
                    _ => ObjAtIndex::new(
                        in_fact.element.clone(),
                        Number::new((index + 1).to_string()).into(),
                    )
                    .into(),
                }
            };
            insert_symbol_substitution(&mut field_map, &field.binding, field_obj);
        }

        for fact in def.equivalent_facts.iter() {
            let after_header = self.inst_fact(
                fact,
                &header_map,
                ParamObjType::DefHeader,
                Some(in_fact.line_file.clone()),
            )?;
            let instantiated_fact = self.inst_fact(
                &after_header,
                &field_map,
                ParamObjType::DefStructField,
                Some(in_fact.line_file.clone()),
            )?;
            // A structure's equivalent facts are its membership obligations. They
            // may be universal laws, such as associativity, so use the ordinary
            // verifier rather than the restricted atomic builtin path.
            let fact_result = self.verify_fact_full(&instantiated_fact, verify_state)?;
            if !fact_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(fact_result);
        }

        Ok(FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "struct membership: element is in the named structure carrier and satisfies struct equivalent facts".to_string(),
            step_results,
        )
        .into())
    }

    // The cardinality of a finite set is a natural number, hence also an integer, rational, and real.
    // Example: if `A finite_set`, then `finite_set_size(A) $in N` and `finite_set_size(A) $in R`.
    pub(crate) fn verify_finite_set_size_in_standard_number_set(
        &mut self,
        in_fact: &InFact,
        finite_set_size: &FiniteSetSize,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let finite_fact =
            IsFiniteSetFact::new((*finite_set_size.set).clone(), in_fact.line_file.clone());
        let finite_result = self.verify_builtin_rule_premise(&finite_fact.into(), builtin_state)?;
        if finite_result.is_true() {
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "finite_set_size of a finite set is a natural number",
                    vec![finite_result],
                ),
            );
        }
        Ok((StmtUnknown::new()).into())
    }

    // A finite-set extremum is an element of its source set.  If that set is
    // known to lie in a standard numeric set, the extremum inherits the type.
    // Examples: `finite_set_max(S) $in S` and `S $subset N` => `finite_set_max(S) $in N`.
    pub(super) fn maybe_verify_in_fact_finite_set_extremum(
        &mut self,
        in_fact: &InFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let source_set = match &in_fact.element {
            Obj::FiniteSetMax(extremum) => extremum.set.as_ref(),
            Obj::FiniteSetMin(extremum) => extremum.set.as_ref(),
            _ => return Ok(None),
        };

        if objs_equal_with_nested_binder_alpha_equivalence(source_set, &in_fact.set) {
            let rule_name = match &in_fact.element {
                Obj::FiniteSetMax(_) => "finite_set_max: the maximum belongs to its set",
                Obj::FiniteSetMin(_) => "finite_set_min: the minimum belongs to its set",
                _ => unreachable!(),
            };
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    rule_name.to_string(),
                    Vec::new(),
                )
                .into(),
            ));
        }

        if !matches!(in_fact.set, Obj::StandardSet(_)) {
            return Ok(Some((StmtUnknown::new()).into()));
        }

        // A finite-set extremum is already defined as a member of its source.
        // Check the source carrier structurally in this same direct rule instead
        // of spending a second builtin-rule layer on `finite_set_max(S) $in S`.
        // Example: `n1, n2 N+` implies `finite_set_max({n1, n2}) $in N+`.
        let Some(type_results) = self.verify_finite_set_extremum_source_in_standard_set(
            source_set,
            &in_fact.set,
            &in_fact.line_file,
            builtin_state,
        )?
        else {
            return Ok(Some((StmtUnknown::new()).into()));
        };

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "finite-set extremum: member of a standard numeric superset".to_string(),
                type_results,
            )
            .into(),
        ))
    }

    fn verify_finite_set_extremum_source_in_standard_set(
        &mut self,
        source_set: &Obj,
        standard_set: &Obj,
        line_file: &LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        match source_set {
            Obj::ListSet(list_set) => {
                let mut results = Vec::new();
                for element in &list_set.list {
                    let element_in_standard_set: AtomicFact = InFact::new(
                        element.as_ref().clone(),
                        standard_set.clone(),
                        line_file.clone(),
                    )
                    .into();
                    let result =
                        self.verify_builtin_rule_premise(&element_in_standard_set, builtin_state)?;
                    if !result.is_true() {
                        return Ok(None);
                    }
                    results.push(result);
                }
                Ok(Some(results))
            }
            Obj::Union(union) => self.verify_two_finite_set_parts_in_standard_set(
                &union.left,
                &union.right,
                standard_set,
                line_file,
                builtin_state,
            ),
            Obj::Intersect(intersect) => self.verify_finite_set_extremum_source_in_standard_set(
                &intersect.left,
                standard_set,
                line_file,
                builtin_state,
            ),
            Obj::SetMinus(set_minus) => self.verify_finite_set_extremum_source_in_standard_set(
                &set_minus.left,
                standard_set,
                line_file,
                builtin_state,
            ),
            Obj::SetBuilder(set_builder) => self.verify_finite_set_extremum_source_in_standard_set(
                &set_builder.param_set,
                standard_set,
                line_file,
                builtin_state,
            ),
            _ => {
                let subset_fact: AtomicFact =
                    SubsetFact::new(source_set.clone(), standard_set.clone(), line_file.clone())
                        .into();
                let result = self.verify_builtin_rule_premise(&subset_fact, builtin_state)?;
                if result.is_true() {
                    Ok(Some(vec![result]))
                } else {
                    Ok(None)
                }
            }
        }
    }

    fn verify_two_finite_set_parts_in_standard_set(
        &mut self,
        left: &Obj,
        right: &Obj,
        standard_set: &Obj,
        line_file: &LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let Some(mut left_results) = self.verify_finite_set_extremum_source_in_standard_set(
            left,
            standard_set,
            line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(mut right_results) = self.verify_finite_set_extremum_source_in_standard_set(
            right,
            standard_set,
            line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        left_results.append(&mut right_results);
        Ok(Some(left_results))
    }

    // Membership is monotone along one known direct set-inclusion edge.
    // Example: `x $in A` plus `A $subset B`, `B $superset A`, or
    // `A $in power_set(B)` proves `x $in B`.
    pub(super) fn verify_in_fact_by_known_direct_superset(
        &self,
        in_fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let goal: AtomicFact = in_fact.clone().into();
        let goal_module_names = self.atomic_fact_referenced_module_names(&goal);
        let element_keys =
            self.all_objs_equal_to_arg_for_known_atomic_fact(&in_fact.element, &goal_module_names);
        let target_set_keys =
            self.all_objs_equal_to_arg_for_known_atomic_fact(&in_fact.set, &goal_module_names);

        let mut owner_memberships = Vec::new();
        for environment in self.iter_environments_from_top() {
            Self::collect_owner_memberships_from_environment(
                environment,
                &element_keys,
                &mut owner_memberships,
            );
        }
        for module_name in goal_module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                Self::collect_owner_memberships_from_environment(
                    environment,
                    &element_keys,
                    &mut owner_memberships,
                );
            }
        }

        for owner_membership in owner_memberships {
            let owner_atomic_fact: AtomicFact = owner_membership.clone().into();
            let mut edge_module_names = goal_module_names.clone();
            for module_name in self.atomic_fact_referenced_module_names(&owner_atomic_fact) {
                if !edge_module_names.contains(&module_name) {
                    edge_module_names.push(module_name);
                }
            }
            let owner_set_keys = self.all_objs_equal_to_arg_for_known_atomic_fact(
                &owner_membership.set,
                &edge_module_names,
            );

            let mut inclusion_evidence = Vec::new();
            for environment in self.iter_environments_from_top() {
                Self::collect_direct_superset_evidence_from_environment(
                    environment,
                    &owner_set_keys,
                    &target_set_keys,
                    &mut inclusion_evidence,
                );
            }
            for module_name in edge_module_names.iter() {
                for environment in self.imported_module_environments(module_name) {
                    Self::collect_direct_superset_evidence_from_environment(
                        environment,
                        &owner_set_keys,
                        &target_set_keys,
                        &mut inclusion_evidence,
                    );
                }
            }

            let Some(inclusion_fact) = inclusion_evidence.into_iter().next() else {
                continue;
            };
            let membership_result =
                Self::stmt_result_for_indexed_fact(owner_atomic_fact, "known owner membership");
            let inclusion_result =
                Self::stmt_result_for_indexed_fact(inclusion_fact, "known direct set inclusion");
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "membership through a known direct set inclusion".to_string(),
                    vec![membership_result, inclusion_result],
                )
                .into(),
            );
        }

        Ok(StmtUnknown::new().into())
    }

    fn collect_owner_memberships_from_environment(
        environment: &Environment,
        element_keys: &[ObjString],
        owner_memberships: &mut Vec<InFact>,
    ) {
        for element_key in element_keys {
            let Some(owner_sets) = environment.known_owner_sets.get(element_key) else {
                continue;
            };
            for owner_membership in owner_sets.values() {
                if !owner_memberships
                    .iter()
                    .any(|known| known.to_string() == owner_membership.to_string())
                {
                    owner_memberships.push(owner_membership.clone());
                }
            }
        }
    }

    fn collect_direct_superset_evidence_from_environment(
        environment: &Environment,
        owner_set_keys: &[ObjString],
        target_set_keys: &[ObjString],
        evidence: &mut Vec<AtomicFact>,
    ) {
        for owner_set_key in owner_set_keys {
            let Some(direct_supersets) = environment.known_direct_supersets.get(owner_set_key)
            else {
                continue;
            };
            for target_set_key in target_set_keys {
                let Some(inclusion_fact) = direct_supersets.get(target_set_key) else {
                    continue;
                };
                if !evidence
                    .iter()
                    .any(|known| known.to_string() == inclusion_fact.to_string())
                {
                    evidence.push(inclusion_fact.clone());
                }
            }
        }
    }

    fn stmt_result_for_indexed_fact(indexed_fact: AtomicFact, detail: &str) -> StmtResult {
        let fact: Fact = indexed_fact.into();
        FactualStmtSuccess::new_with_verified_by_known_fact(
            fact.clone(),
            VerifiedByResult::cited_fact(fact.clone(), fact, Some(detail.to_string())),
            Vec::new(),
        )
        .into()
    }
}
