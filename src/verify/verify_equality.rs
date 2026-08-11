use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let builtin_goal: AtomicFact = equal_fact.clone().into();
        let mut result = self
            .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                &builtin_goal,
            )?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_atomic_fact_with_builtin_strategy(&builtin_goal)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_equality_with_known_equalities(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact.line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verified_by_arg_to_arg = self
                .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                    &equal_fact.left,
                    &equal_fact.right,
                    verify_state,
                    equal_fact.line_file.clone(),
                )?;
            if verified_by_arg_to_arg {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        equal_fact.clone().into(),
                        same_shape_and_equal_args_reason(&equal_fact.left, &equal_fact.right),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        if verify_state.is_round_0() && verify_state.equality_can_use_known_forall {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();
            result = self
                .verify_atomic_fact_with_known_forall(&builtin_goal, &verify_state_add_one_round)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(crate) fn verify_equality_with_known_equalities(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // The outer atomic-fact verifier must have discharged well-definedness
        // before replay. This keeps `unfold_known_fn_application_once` on its
        // substitution-only path: no carrier or domain proof search is repeated.
        if !verify_state.is_round_0()
            || !verify_state.well_defined_already_verified
            || self.known_equality_candidate_replay_depth != 0
        {
            return Ok((StmtUnknown::new()).into());
        }

        let left_string = obj_equality_key(left);
        let right_string = obj_equality_key(right);

        let known_pairs =
            self.collect_known_equality_pairs_from_envs(&left_string, &right_string, left, right);
        let mut tried_pairs = HashSet::new();
        for (known_left, known_right) in known_pairs {
            let mut left_candidates = vec![left.clone()];
            if let Some(known_left) = known_left {
                let mut left_keys = HashSet::from([left_string.clone()]);
                for candidate in known_left.iter() {
                    if left_keys.insert(obj_equality_key(candidate)) {
                        left_candidates.push(candidate.clone());
                    }
                }
            }

            let mut right_candidates = vec![right.clone()];
            if let Some(known_right) = known_right {
                let mut right_keys = HashSet::from([right_string.clone()]);
                for candidate in known_right.iter() {
                    if right_keys.insert(obj_equality_key(candidate)) {
                        right_candidates.push(candidate.clone());
                    }
                }
            }

            for candidate_left in left_candidates.iter() {
                for candidate_right in right_candidates.iter() {
                    let pair_key = (
                        obj_equality_key(candidate_left),
                        obj_equality_key(candidate_right),
                    );
                    if !tried_pairs.insert(pair_key) {
                        continue;
                    }

                    self.known_equality_candidate_replay_depth += 1;
                    let candidate_result = self.try_verify_one_equality_representative_pair(
                        left,
                        right,
                        candidate_left,
                        candidate_right,
                        line_file.clone(),
                        verify_state,
                    );
                    self.known_equality_candidate_replay_depth -= 1;
                    if let Some(result) = candidate_result? {
                        return Ok(result);
                    }
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn try_verify_one_equality_representative_pair(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        candidate_left: &Obj,
        candidate_right: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if self.objs_are_congruent_by_replay_safe_equality_routes(
            candidate_left,
            candidate_right,
            line_file.clone(),
        )? {
            return Ok(Some(known_equality_representative_replay_success(
                statement_left,
                statement_right,
                candidate_left,
                candidate_right,
                line_file,
                "known non-forall equality, pure computation, bounded symbolic normalization, anonymous-function beta reduction, or structural congruence",
            )));
        }

        if let Some(done) = self.try_one_side_checked_definition_replay(
            statement_left,
            statement_right,
            candidate_left,
            candidate_right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(Some(done));
        }
        self.try_one_side_checked_definition_replay(
            statement_left,
            statement_right,
            candidate_right,
            candidate_left,
            line_file,
            verify_state,
        )
    }

    fn try_one_side_checked_definition_replay(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        application_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // Replay exactly one checked outer definition. Comparison uses only
        // known non-forall facts, obligation-free computation/normalization,
        // and constructor descent; it cannot instantiate forall facts or
        // reopen definition replay.
        // Structured definition provenance is a Litex-to-Lean capture concern. Keep
        // ordinary Litex verification on its established replay path so the
        // compiler cannot perturb rule selection or environment effects.
        let checked_function_source = if self.captures_litex_to_lean_well_definedness() {
            self.checked_function_definition_replay_source(application_side)?
        } else {
            None
        };
        let reduced = match self.unfold_known_fn_application_once(application_side, verify_state)? {
            Some(reduced) => reduced,
            None => {
                let Some(set_builder) = self.get_obj_equal_to_set_builder(application_side) else {
                    return Ok(None);
                };
                set_builder.into()
            }
        };
        let mut comparison_candidates = vec![reduced.clone()];
        if let Some(beta_reduced) =
            self.beta_reduce_complete_anonymous_application_once(&reduced)?
        {
            if !objs_equal_with_nested_binder_alpha_equivalence(&reduced, &beta_reduced) {
                comparison_candidates.push(beta_reduced);
            }
        }

        for comparison_candidate in comparison_candidates {
            let alpha_equal =
                objs_equal_with_nested_binder_alpha_equivalence(&comparison_candidate, other_side);
            let compared_equal = alpha_equal
                || self.objs_are_congruent_by_replay_safe_equality_routes(
                    &comparison_candidate,
                    other_side,
                    line_file.clone(),
                )?;
            if !compared_equal {
                continue;
            }

            let reason = format!(
                "one checked definition replay `{}` = `{}`",
                application_side, comparison_candidate
            );
            let application_is_left =
                objs_equal_with_nested_binder_alpha_equivalence(statement_left, application_side);
            let application_is_right =
                objs_equal_with_nested_binder_alpha_equivalence(statement_right, application_side);
            if let (Some((definition_object, defining_equality, defining_equality_fact_id)), true) = (
                checked_function_source.clone(),
                application_is_left ^ application_is_right,
            ) {
                let fact: Fact = EqualFact::new(
                    statement_left.clone(),
                    statement_right.clone(),
                    line_file.clone(),
                )
                .into();
                let evidence = CheckedDefinitionReplayEvidence {
                    definition_object,
                    defining_equality,
                    defining_equality_fact_id,
                    application_side: application_side.clone(),
                    reduced: comparison_candidate.clone(),
                    other_side: other_side.clone(),
                    application_is_left,
                    reduced_matches_other_by_alpha: alpha_equal,
                };
                let verified_by = VerifiedByResult::fact_with_checked_definition_replay(
                    fact.clone(),
                    evidence,
                    Some(reason),
                );
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_known_fact(
                        fact,
                        verified_by,
                        Vec::new(),
                    )
                    .into(),
                ));
            }
            return Ok(Some(known_equality_representative_replay_success(
                statement_left,
                statement_right,
                application_side,
                other_side,
                line_file,
                &reason,
            )));
        }
        Ok(None)
    }

    fn checked_function_definition_replay_source(
        &self,
        application: &Obj,
    ) -> Result<Option<(Obj, Fact, FactId)>, RuntimeError> {
        let Obj::FnObj(function_application) = application else {
            return Ok(None);
        };
        if function_application.body.is_empty() {
            return Ok(None);
        }
        let definition_object: Obj = match function_application.head.as_ref() {
            FnObjHead::Identifier(_) | FnObjHead::IdentifierWithMod(_) => {
                (*function_application.head).clone().into()
            }
            _ => return Ok(None),
        };
        let Some((body, equal_to, line_file)) =
            self.get_known_fn_body_and_equal_to_for_obj(&definition_object)
        else {
            return Ok(None);
        };
        let anonymous_function = AnonymousFn {
            body,
            equal_to: Box::new(equal_to),
        };
        let defining_equality: Fact = EqualFact::new(
            definition_object.clone(),
            anonymous_function.into(),
            line_file,
        )
        .into();
        let Some(defining_equality_fact_id) = self.known_fact_id_for_fact(&defining_equality)?
        else {
            return Ok(None);
        };
        Ok(Some((
            definition_object,
            defining_equality,
            defining_equality_fact_id,
        )))
    }

    /// Build equality closures without merging the underlying environments.
    fn collect_known_equality_pairs_from_envs(
        &self,
        left_string: &str,
        right_string: &str,
        left: &Obj,
        right: &Obj,
    ) -> Vec<(Option<Rc<Vec<Obj>>>, Option<Rc<Vec<Obj>>>)> {
        let current_environments = self.iter_environments_from_top().collect::<Vec<_>>();
        let mut pairs = vec![(
            known_equality_class_across_environments(
                &current_environments,
                &[left_string.to_string()],
            ),
            known_equality_class_across_environments(
                &current_environments,
                &[right_string.to_string()],
            ),
        )];
        let mut module_names = self.obj_referenced_module_names(left);
        for module_name in self.obj_referenced_module_names(right) {
            if !module_names
                .iter()
                .any(|existing_module_name| existing_module_name == &module_name)
            {
                module_names.push(module_name);
            }
        }
        for module_name in module_names.iter() {
            let environments = self.imported_module_environments(module_name);
            if environments.is_empty() {
                continue;
            }
            pairs.push((
                known_equality_class_across_environments(&environments, &[left_string.to_string()]),
                known_equality_class_across_environments(
                    &environments,
                    &[right_string.to_string()],
                ),
            ));
        }
        pairs
    }

    fn verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        right_left: &Obj,
        right_right: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_left,
            right_left,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_right,
            right_right,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        Ok(true)
    }

    fn verify_unary_objs_are_equal_when_their_only_args_are_equal(
        &mut self,
        left_value: &Obj,
        right_value: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let result = self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
            left_value,
            right_value,
            verify_state,
            equality_line_file.clone(),
        )?;
        if result.is_true() {
            return Ok(true);
        }
        Ok(false)
    }

    fn verify_function_args_are_equal_for_iterated_operator(
        &mut self,
        left_func: &Obj,
        right_func: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        // Iterated operators such as sum/product compare their summand
        // functions extensionally. Example:
        // `sum(1, n, fn(x Z) Z {f(x)}) = sum(1, n, fn(y Z) Z {f(y)})`.
        self.verify_unary_objs_are_equal_when_their_only_args_are_equal(
            left_func,
            right_func,
            verify_state,
            equality_line_file,
        )
    }

    pub(crate) fn verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
        &mut self,
        left_obj: &Obj,
        right_obj: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        match (left_obj, right_obj) {
            (Obj::Sum(left), Obj::Sum(right)) => {
                if !self.verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left.start,
                    &left.end,
                    &right.start,
                    &right.end,
                    verify_state,
                    equality_line_file.clone(),
                )? {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::SumOfFiniteSet(left), Obj::SumOfFiniteSet(right)) => {
                if !self
                    .verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        left.set.as_ref(),
                        right.set.as_ref(),
                        verify_state,
                        equality_line_file.clone(),
                    )?
                    .is_true()
                {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::ProductOfFiniteSet(left), Obj::ProductOfFiniteSet(right)) => {
                if !self
                    .verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        left.set.as_ref(),
                        right.set.as_ref(),
                        verify_state,
                        equality_line_file.clone(),
                    )?
                    .is_true()
                {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            (Obj::Product(left), Obj::Product(right)) => {
                if !self.verify_binary_objs_are_equal_when_both_corresponding_args_are_equal(
                    &left.start,
                    &left.end,
                    &right.start,
                    &right.end,
                    verify_state,
                    equality_line_file.clone(),
                )? {
                    return Ok(false);
                }
                self.verify_function_args_are_equal_for_iterated_operator(
                    left.func.as_ref(),
                    right.func.as_ref(),
                    verify_state,
                    equality_line_file,
                )
            }
            _ => Self::same_shape_and_corresponding_args_match(
                left_obj,
                right_obj,
                &mut |left_arg, right_arg| {
                    self.verify_two_objs_equal_by_builtin_rules_and_known_equalities(
                        left_arg,
                        right_arg,
                        verify_state,
                        equality_line_file.clone(),
                    )
                    .map(|result| result.is_true())
                },
            ),
        }
    }

    fn verify_two_objs_equal_by_builtin_rules_and_known_equalities(
        &mut self,
        left_obj: &Obj,
        right_obj: &Obj,
        verify_state: &UseContextVerifyState,
        equality_line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result = self
            .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                &EqualFact::new(
                    left_obj.clone(),
                    right_obj.clone(),
                    equality_line_file.clone(),
                )
                .into(),
            )?;
        if result.is_true() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(
                        left_obj.clone(),
                        right_obj.clone(),
                        equality_line_file.clone(),
                    )
                    .into(),
                    "builtin rules".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        result = self.verify_equality_with_known_equalities(
            left_obj,
            right_obj,
            equality_line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        let verified_by_arg_to_arg = self
            .verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(
                left_obj,
                right_obj,
                verify_state,
                equality_line_file.clone(),
            )?;
        if verified_by_arg_to_arg {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    EqualFact::new(left_obj.clone(), right_obj.clone(), equality_line_file).into(),
                    same_shape_and_equal_args_reason(left_obj, right_obj),
                    Vec::new(),
                ))
                .into(),
            );
        }

        Ok((StmtUnknown::new()).into())
    }
}

fn known_equality_class_across_environments(
    environments: &[&Environment],
    initial_keys: &[String],
) -> Option<Rc<Vec<Obj>>> {
    let mut keys = initial_keys.to_vec();
    let mut known_keys = keys.iter().cloned().collect::<HashSet<_>>();
    let mut objects = Vec::new();
    let mut object_keys = HashSet::new();
    let mut scanned_classes = HashSet::new();
    let mut next_index = 0;
    let mut found_equality = false;

    while next_index < keys.len() {
        let current = keys[next_index].clone();
        next_index += 1;
        for (environment_index, environment) in environments.iter().enumerate() {
            let Some((class_id, _, equivalent_objects)) =
                environment.known_equality.get_with_class_id(&current)
            else {
                continue;
            };
            found_equality = true;
            if !scanned_classes.insert((environment_index, class_id)) {
                continue;
            }
            for object in equivalent_objects.iter() {
                let object_key = obj_equality_key(object);
                if known_keys.insert(object_key.clone()) {
                    keys.push(object_key.clone());
                }
                if object_keys.insert(object_key) {
                    objects.push(object.clone());
                }
            }
        }
    }

    if found_equality {
        Some(Rc::new(objects))
    } else {
        None
    }
}

fn same_shape_and_equal_args_reason(left_obj: &Obj, right_obj: &Obj) -> String {
    match (left_obj, right_obj) {
        (Obj::FnObj(_), Obj::FnObj(_)) => {
            "the function parts are equal, and the function arguments are equal one by one"
                .to_string()
        }
        _ => "the corresponding builtin-object arguments are equal one by one".to_string(),
    }
}

fn known_equality_representative_replay_success(
    statement_left: &Obj,
    statement_right: &Obj,
    candidate_left: &Obj,
    candidate_right: &Obj,
    line_file: LineFile,
    reason: &str,
) -> StmtResult {
    let fact: Fact =
        EqualFact::new(statement_left.clone(), statement_right.clone(), line_file).into();
    let msg = format!(
        "{} via known equality representatives `{}` and `{}`; comparison nodes may use stored non-forall equalities, pure computation, bounded symbolic normalization, capture-avoiding beta reduction of complete anonymous-function applications, or constructor descent, but never ordinary builtin rules, known forall, or recursive definition replay",
        reason, candidate_left, candidate_right
    );
    let verified_by = VerifiedByResult::fact_with_note(fact.clone(), Some(msg));
    FactualStmtSuccess::new_with_verified_by_known_fact(fact, verified_by, Vec::new()).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_equality_runs_only_from_the_outer_round() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("structural_equality_outer_round");

        let a: Obj = Identifier::new("A".to_string()).into();
        let b: Obj = Identifier::new("B".to_string()).into();
        let union_ab: Obj = Union::new(a.clone(), b.clone()).into();
        let union_ba: Obj = Union::new(b, a).into();
        let left: Obj =
            StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ab]).into();
        let right: Obj =
            StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ba]).into();
        let equal_fact = EqualFact::new(left.clone(), right.clone(), default_line_file());
        assert!(runtime
            .verify_objs_are_equal_by_known_equality(&left, &right, default_line_file())
            .is_unknown());
        assert!(runtime
            .verify_equal_fact(&equal_fact, &UseContextVerifyState::new(1, true))
            .expect("later-round equality verification")
            .is_unknown());
        assert!(runtime
            .verify_equal_fact(&equal_fact, &UseContextVerifyState::new(0, true))
            .expect("outer-round equality verification")
            .is_true());
    }

    #[test]
    fn checked_definition_replay_uses_only_safe_leaves() {
        let source = include_str!("verify_equality.rs");
        let replay_impl = source
            .split("fn try_verify_one_equality_representative_pair(")
            .nth(1)
            .expect("representative replay implementation must exist")
            .split("/// Build equality closures")
            .next()
            .expect("equality closure implementation must follow representative replay");

        assert!(replay_impl.contains("objs_are_congruent_by_replay_safe_equality_routes"));
        assert!(source.contains("!verify_state.well_defined_already_verified"));
        assert!(!replay_impl.contains("resolve_obj"));
        assert!(!replay_impl.contains("verify_atomic_fact_with_known_forall"));
        assert!(!replay_impl
            .contains("verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules"));
        assert!(!replay_impl.contains("verify_equal_fact("));

        let structural_source = include_str!("verify_builtin_rules/equality_structural.rs");
        let replay_safe_comparator = structural_source
            .split("fn objs_are_congruent_by_replay_safe_equality_routes(")
            .nth(1)
            .expect("replay-safe comparator must exist")
            .split("pub(crate) fn same_shape_and_corresponding_args_match")
            .next()
            .expect("central structural matcher must follow the replay-safe comparator");
        assert!(replay_safe_comparator
            .contains("verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation"));
        assert!(replay_safe_comparator.contains("beta_reduce_complete_anonymous_application_once"));
        assert!(!replay_safe_comparator.contains("verify_atomic_fact_with_one_builtin_rule"));
        assert!(!replay_safe_comparator.contains("verify_atomic_fact_with_builtin_rules_inner"));
        assert!(!replay_safe_comparator.contains("resolve_obj"));
        assert!(!replay_safe_comparator.contains("verify_atomic_fact_with_known_forall"));
        assert!(!replay_safe_comparator.contains("verify_equal_fact"));

        let atomic_source = include_str!("verify_atomic_fact.rs");
        assert!(atomic_source.contains("known_equality_candidate_replay_depth != 0"));
        assert!(atomic_source
            .contains("verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation"));
        let forall_source = include_str!("verify_atomic_fact_with_known_forall.rs");
        assert!(forall_source.contains("known_equality_candidate_replay_depth != 0"));

        let equality_builtin_source = include_str!("verify_builtin_rules/equality_dispatch.rs");
        let direct_cart_forall_lookup = equality_builtin_source
            .split("fn verify_exact_cart_projection_from_known_forall(")
            .nth(1)
            .expect("direct cart-forall lookup must exist")
            .split("fn try_verify_empty_set_equality_from_not_nonempty(")
            .next()
            .expect("the next equality builtin must follow cart-forall lookup");
        assert!(direct_cart_forall_lookup.contains("known_equality_candidate_replay_depth != 0"));

        let set_membership_source =
            include_str!("verify_builtin_rules/in_fact_builtin/set_membership.rs");
        assert!(
            set_membership_source
                .matches("known_equality_candidate_replay_depth != 0")
                .count()
                >= 2
        );
        assert!(set_membership_source.contains("self.known_equality_candidate_replay_depth == 0"));
    }

    #[test]
    fn replay_safe_comparator_allows_computation_and_bounded_symbolic_normalization() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("replay_safe_computation");
        let one: Obj = Number::new("1".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();
        let one_plus_one: Obj = Add::new(one.clone(), one).into();

        assert!(runtime.objs_are_congruent_by_known_equalities(
            &one_plus_one,
            &two,
            default_line_file(),
        ));
        assert!(runtime
            .objs_are_congruent_by_replay_safe_equality_routes(
                &one_plus_one,
                &two,
                default_line_file(),
            )
            .expect("replay-safe comparison"));

        let x: Obj = Identifier::new("x".to_string()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let x_plus_zero: Obj = Add::new(x.clone(), zero).into();
        assert!(runtime
            .objs_are_congruent_by_replay_safe_equality_routes(
                &x_plus_zero,
                &x,
                default_line_file(),
            )
            .expect("bounded symbolic normalization"));

        let y: Obj = Identifier::new("y".to_string()).into();
        let x_minus_y: Obj = Sub::new(x.clone(), y.clone()).into();
        let y_minus_x: Obj = Sub::new(y.clone(), x.clone()).into();
        let abs_x_minus_y: Obj = Abs::new(x_minus_y).into();
        let abs_y_minus_x: Obj = Abs::new(y_minus_x).into();
        assert!(runtime
            .objs_are_congruent_by_replay_safe_equality_routes(
                &abs_x_minus_y,
                &abs_y_minus_x,
                default_line_file(),
            )
            .expect("absolute-value sign normalization"));

        let abs_x: Obj = Abs::new(x).into();
        let abs_y: Obj = Abs::new(y).into();
        assert!(!runtime
            .objs_are_congruent_by_replay_safe_equality_routes(&abs_x, &abs_y, default_line_file())
            .expect("unrelated absolute values must not compare equal"));
    }
}
