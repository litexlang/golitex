//! Known universal fact selection, matching, and instantiation.

use super::*;

impl Runtime {
    pub fn verify_atomic_fact_with_known_forall(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact_with_known_forall(equal_fact, verify_state)
            }
            _ => {
                self.verify_non_equational_atomic_fact_with_known_forall(atomic_fact, verify_state)
            }
        }
    }

    pub fn verify_non_equational_atomic_fact_with_known_forall(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        known_forall_profile::record_entry();
        if let Some(fact_verified) =
            self.verify_atomic_fact_with_known_forall_forward(atomic_fact, verify_state)?
        {
            known_forall_profile::record_success();
            let result = fact_verified.into();
            return Ok(result);
        }

        known_forall_profile::record_unknown();
        Ok((UnknownGenericStmtResult::new()).into())
    }

    pub fn verify_equal_fact_with_known_forall(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let atomic_fact: AtomicFact = equal_fact.clone().into();
        known_forall_profile::record_entry();
        if let Some(fact_verified) =
            self.verify_atomic_fact_with_known_forall_forward(&atomic_fact, verify_state)?
        {
            known_forall_profile::record_success();
            let result = fact_verified.into();
            return Ok(result);
        }

        if let Some(fact_verified) = self
            .try_verify_equal_fact_with_known_forall_after_nested_rational_normalization(
                equal_fact,
                verify_state,
            )?
        {
            known_forall_profile::record_success();
            let result = fact_verified.into();
            return Ok(result);
        }

        let fact_with_reversed_args: AtomicFact = self
            .new_equal_fact(
                equal_fact.right.clone(),
                equal_fact.left.clone(),
                equal_fact.line_file.clone(),
            )
            .into();
        if let Some(fact_verified) =
            self.try_verify_with_known_forall_facts_in_envs(&fact_with_reversed_args, verify_state)?
        {
            known_forall_profile::record_success();
            let reversed_result = self.complete_atomic_fact_proof_result(
                &fact_with_reversed_args,
                fact_verified.into(),
                verify_state,
            )?;
            let target: Fact = equal_fact.clone().into();
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    target,
                    "equality symmetry".to_string(),
                    BuiltinRuleEvidence::EqualitySymmetry,
                    vec![reversed_result],
                )
                .into(),
            );
        }

        known_forall_profile::record_unknown();
        Ok((UnknownGenericStmtResult::new()).into())
    }

    /// Match one side of a stored universally quantified equality, instantiate
    /// the complete equality, and then admit only obligation-free arithmetic
    /// normalization between that instance and the requested equality.
    ///
    /// Recursive `have fn ... by induc` definitions store their case equations
    /// as ordinary conditional forall facts.  For a positive recursive case,
    /// matching `f(k)` against `f(n + 1)` selects `k := n + 1`; the stored
    /// right-hand side then contains `(n + 1) - 1`, which normalizes to `n`.
    /// Case requirements are still checked independently, so an argument whose
    /// branch is unknown cannot be unfolded by this route.
    pub(in crate::verification) fn try_verify_equal_fact_with_known_forall_after_nested_rational_normalization(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let target_atomic: AtomicFact = equal_fact.clone().into();
        let lookup_key = (target_atomic.key(), target_atomic.has_positive_polarity());
        let candidates: Vec<(AtomicFact, Rc<StoredForallConclusionReference>)> = self
            .iter_environments_from_top()
            .flat_map(|environment| {
                environment
                    .facts
                    .forall_conclusions
                    .atomic_with_parameterized_head
                    .get(&lookup_key)
                    .into_iter()
                    .flat_map(|facts| facts.iter())
                    .chain(
                        environment
                            .facts
                            .forall_conclusions
                            .atomic_by_argument_shape
                            .get(&lookup_key)
                            .into_iter()
                            .flat_map(|shape_map| shape_map.values())
                            .flat_map(|facts| facts.iter()),
                    )
            })
            .cloned()
            .collect();

        for (candidate, known_forall) in candidates {
            if let Some(success) = self
                .try_verify_known_forall_equality_candidate_after_nested_rational_normalization(
                    candidate,
                    known_forall,
                    &target_atomic,
                    &target_atomic,
                    verify_state,
                )?
            {
                return Ok(Some(success));
            }
        }

        let module_names = self.atomic_fact_referenced_module_names(&target_atomic);
        for module_name in module_names.iter() {
            let module_local_identifiers =
                self.imported_module_identifier_to_local_obj_map(module_name);
            let matching_target = self.inst_atomic_fact(
                &target_atomic,
                &module_local_identifiers,
                SubstitutionMode::Named,
                None,
            )?;
            let imported_candidates = self
                .imported_module_environments(module_name)
                .into_iter()
                .flat_map(|environment| {
                    environment
                        .facts
                        .forall_conclusions
                        .atomic_with_parameterized_head
                        .get(&lookup_key)
                        .into_iter()
                        .flat_map(|facts| facts.iter())
                        .chain(
                            environment
                                .facts
                                .forall_conclusions
                                .atomic_by_argument_shape
                                .get(&lookup_key)
                                .into_iter()
                                .flat_map(|shape_map| shape_map.values())
                                .flat_map(|facts| facts.iter()),
                        )
                })
                .cloned()
                .collect::<Vec<_>>();
            for (candidate, known_forall) in imported_candidates {
                if let Some(success) = self
                    .try_verify_known_forall_equality_candidate_after_nested_rational_normalization(
                        candidate,
                        known_forall,
                        &matching_target,
                        &target_atomic,
                        verify_state,
                    )?
                {
                    return Ok(Some(success));
                }
            }
        }
        Ok(None)
    }

    pub(in crate::verification) fn try_verify_known_forall_equality_candidate_after_nested_rational_normalization(
        &mut self,
        candidate: AtomicFact,
        known_forall: Rc<StoredForallConclusionReference>,
        matching_target: &AtomicFact,
        given_target: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let (AtomicFact::EqualFact(candidate_equality), AtomicFact::EqualFact(matching_equality)) =
            (&candidate, matching_target)
        else {
            return Ok(None);
        };
        for (candidate_anchor, target_anchor) in [
            (&candidate_equality.left, &matching_equality.left),
            (&candidate_equality.right, &matching_equality.right),
        ] {
            known_forall_profile::record_candidate_attempt(KnownForallSearchPhase::OtherShape);
            let Some((mut arg_map, _)) = self.match_args_in_fact_with_known_forall_bindings(
                &[candidate_anchor],
                &[target_anchor],
                &known_forall.params_def,
                None,
            )?
            else {
                continue;
            };
            known_forall_profile::record_arg_match();
            self.complete_known_forall_arg_map_from_known_dom_facts(
                known_forall.as_ref(),
                &mut arg_map,
            )?;
            if !known_forall
                .params_def
                .collect_param_names()
                .iter()
                .all(|param_name| arg_map.contains_key(param_name))
            {
                continue;
            }
            let instantiated =
                self.inst_atomic_fact(&candidate, &arg_map, SubstitutionMode::Exact, None)?;
            if !super::super::known_facts::atomic_facts_align_by_nested_rational_normalization(
                &instantiated,
                matching_target,
            ) {
                continue;
            }
            if let Some(success) = self.verify_args_satisfy_forall_requirements(
                &candidate,
                &known_forall,
                arg_map,
                given_target,
                verify_state,
            )? {
                return Ok(Some(success));
            }
            known_forall_profile::record_requirement_failure();
        }
        Ok(None)
    }

    pub(in crate::verification) fn verify_atomic_fact_with_known_forall_forward(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        if let Some(fact_verified) =
            self.try_verify_with_known_forall_facts_in_envs(atomic_fact, verify_state)?
        {
            return Ok(Some(fact_verified));
        }

        if let Some(resolved_fact) = self.resolved_atomic_fact_for_lookup(atomic_fact) {
            if let Some(mut fact_verified) =
                self.try_verify_with_known_forall_facts_in_envs(&resolved_fact, verify_state)?
            {
                fact_verified = fact_verified.with_verified_fact(atomic_fact.clone().into());
                return Ok(Some(fact_verified));
            }
        }

        Ok(None)
    }

    pub(in crate::verification) fn get_matched_atomic_fact_in_fallback_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_fact: &AtomicFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(AtomicFact, Rc<StoredForallConclusionReference>)>,
        ),
        RuntimeError,
    > {
        let key = given_fact.key();
        let positive_polarity = given_fact.has_positive_polarity();

        let envs_count = self.environment_count();
        let lookup_key = (key.clone(), positive_polarity);
        for i in iterate_from_env_index..envs_count {
            let stack_idx = i;
            let known_forall_facts_count = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                match env
                    .facts
                    .forall_conclusions
                    .atomic_with_parameterized_head
                    .get(&lookup_key)
                {
                    Some(v) => v.len(),
                    None => continue,
                }
            };
            let start_index = if i == iterate_from_env_index {
                iterate_from_known_forall_fact_index
            } else {
                0
            };
            for j in start_index..known_forall_facts_count {
                let entry_idx = known_forall_facts_count - 1 - j;
                let (atomic_fact_in_known_forall, current_known_forall) = {
                    let env = self
                        .environment_by_top_index(stack_idx)
                        .expect("environment index should be valid");
                    let Some(known_forall_facts_in_env) = env
                        .facts
                        .forall_conclusions
                        .atomic_with_parameterized_head
                        .get(&lookup_key)
                    else {
                        continue;
                    };
                    let Some(current_known_forall) = known_forall_facts_in_env.get(entry_idx)
                    else {
                        continue;
                    };
                    (current_known_forall.0.clone(), current_known_forall.clone())
                };
                known_forall_profile::record_candidate_attempt(KnownForallSearchPhase::Fallback);
                let match_result = self.match_atomic_fact_args_against_known_forall_ordered_args(
                    &atomic_fact_in_known_forall,
                    given_fact,
                    &current_known_forall.1.params_def,
                )?;
                if let Some(arg_map) = match_result {
                    known_forall_profile::record_arg_match();
                    return Ok(((i, j), Some(arg_map), Some(current_known_forall)));
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    pub(in crate::verification) fn try_verify_with_fallback_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let mut iterate_from_env_index = 0;
        let mut iterate_from_known_forall_fact_index = 0;

        loop {
            let result = self.get_matched_atomic_fact_in_fallback_known_forall_fact_in_envs(
                iterate_from_env_index,
                iterate_from_known_forall_fact_index,
                atomic_fact,
            )?;
            let ((i, j), arg_map_opt, known_forall_opt) = result;
            match (arg_map_opt, known_forall_opt) {
                (Some(arg_map), Some((atomic_fact_in_known_forall_fact, forall_rc))) => {
                    if let Some(fact_verified) = self.verify_args_satisfy_forall_requirements(
                        &atomic_fact_in_known_forall_fact,
                        &forall_rc,
                        arg_map,
                        atomic_fact,
                        verify_state,
                    )? {
                        return Ok(Some(fact_verified));
                    }
                    known_forall_profile::record_requirement_failure();
                    iterate_from_env_index = i;
                    iterate_from_known_forall_fact_index = j + 1;
                }
                _ => break,
            }
        }

        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        self.try_verify_with_fallback_known_forall_facts_in_imported_modules(
            atomic_fact,
            verify_state,
            &module_names,
        )
    }

    pub(in crate::verification) fn try_verify_with_fallback_known_forall_facts_in_imported_modules(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        module_names: &[String],
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.has_positive_polarity());
        for module_name in module_names.iter() {
            let module_local_identifiers =
                self.imported_module_identifier_to_local_obj_map(module_name);
            let matching_atomic_fact = self.inst_atomic_fact(
                atomic_fact,
                &module_local_identifiers,
                SubstitutionMode::Named,
                None,
            )?;
            let candidates = self
                .imported_module_environments(module_name)
                .into_iter()
                .filter_map(|env| {
                    env.facts
                        .forall_conclusions
                        .atomic_with_parameterized_head
                        .get(&lookup_key)
                })
                .flat_map(|facts| facts.iter().rev().cloned())
                .collect::<Vec<_>>();

            for (atomic_fact_in_known_forall, forall_rc) in candidates {
                if let Some(fact_verified) = self
                    .try_verify_known_forall_candidate_with_matching_fact(
                        KnownForallSearchPhase::Fallback,
                        atomic_fact_in_known_forall,
                        forall_rc,
                        &matching_atomic_fact,
                        atomic_fact,
                        verify_state,
                    )?
                {
                    return Ok(Some(fact_verified));
                }
            }
        }
        Ok(None)
    }

    pub(in crate::verification) fn try_verify_with_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let arg_shape_lookup_keys = atomic_fact_in_forall_lookup_arg_shape_keys(atomic_fact);
        if let Some(fact_verified) = self.try_verify_with_arg_shape_known_forall_facts_in_envs(
            atomic_fact,
            &arg_shape_lookup_keys,
            verify_state,
        )? {
            return Ok(Some(fact_verified));
        }

        if let Some(fact_verified) =
            self.try_verify_with_fallback_known_forall_facts_in_envs(atomic_fact, verify_state)?
        {
            return Ok(Some(fact_verified));
        }

        self.try_verify_with_other_arg_shape_known_forall_facts_in_envs(
            atomic_fact,
            &arg_shape_lookup_keys,
            verify_state,
        )
    }

    pub(in crate::verification) fn try_verify_known_forall_candidate(
        &mut self,
        phase: KnownForallSearchPhase,
        atomic_fact_in_known_forall_fact: AtomicFact,
        forall_rc: Rc<StoredForallConclusionReference>,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        self.try_verify_known_forall_candidate_with_matching_fact(
            phase,
            atomic_fact_in_known_forall_fact,
            forall_rc,
            given_atomic_fact,
            given_atomic_fact,
            verify_state,
        )
    }

    pub(in crate::verification) fn try_verify_known_forall_candidate_with_matching_fact(
        &mut self,
        phase: KnownForallSearchPhase,
        atomic_fact_in_known_forall_fact: AtomicFact,
        forall_rc: Rc<StoredForallConclusionReference>,
        matching_atomic_fact: &AtomicFact,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        known_forall_profile::record_candidate_attempt(phase);
        let match_result = self.match_atomic_fact_args_against_known_forall_ordered_args(
            &atomic_fact_in_known_forall_fact,
            matching_atomic_fact,
            &forall_rc.params_def,
        )?;
        if let Some(arg_map) = match_result {
            known_forall_profile::record_arg_match();
            let fact_verified = self.verify_args_satisfy_forall_requirements(
                &atomic_fact_in_known_forall_fact,
                &forall_rc,
                arg_map,
                given_atomic_fact,
                verify_state,
            )?;
            if fact_verified.is_none() {
                known_forall_profile::record_requirement_failure();
            }
            return Ok(fact_verified);
        }
        Ok(None)
    }

    pub(in crate::verification) fn try_verify_with_arg_shape_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        arg_shape_lookup_keys: &[ForallArgumentShape],
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.has_positive_polarity());
        let envs_count = self.environment_count();
        for stack_idx in 0..envs_count {
            for arg_shape_lookup_key in arg_shape_lookup_keys.iter() {
                if let Some(fact_verified) = self.try_verify_with_arg_shape_key_in_env(
                    stack_idx,
                    &lookup_key,
                    arg_shape_lookup_key,
                    atomic_fact,
                    verify_state,
                    KnownForallSearchPhase::ExactShape,
                )? {
                    return Ok(Some(fact_verified));
                }
            }
        }
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        for module_name in module_names.iter() {
            for arg_shape_lookup_key in arg_shape_lookup_keys.iter() {
                if let Some(fact_verified) = self
                    .try_verify_with_arg_shape_key_in_imported_module_env(
                        module_name,
                        &lookup_key,
                        arg_shape_lookup_key,
                        atomic_fact,
                        verify_state,
                        KnownForallSearchPhase::ExactShape,
                    )?
                {
                    return Ok(Some(fact_verified));
                }
            }
        }
        Ok(None)
    }

    pub(in crate::verification) fn try_verify_with_other_arg_shape_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        arg_shape_lookup_keys: &[ForallArgumentShape],
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.has_positive_polarity());
        let envs_count = self.environment_count();
        for stack_idx in 0..envs_count {
            let arg_shape_keys = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                let Some(arg_shape_map) = env
                    .facts
                    .forall_conclusions
                    .atomic_by_argument_shape
                    .get(&lookup_key)
                else {
                    continue;
                };
                arg_shape_map
                    .keys()
                    .filter(|key| !arg_shape_lookup_keys.contains(key))
                    .cloned()
                    .collect::<Vec<_>>()
            };
            for arg_shape_key in arg_shape_keys.iter() {
                if let Some(fact_verified) = self.try_verify_with_arg_shape_key_in_env(
                    stack_idx,
                    &lookup_key,
                    arg_shape_key,
                    atomic_fact,
                    verify_state,
                    KnownForallSearchPhase::OtherShape,
                )? {
                    return Ok(Some(fact_verified));
                }
            }
        }
        let module_names = self.atomic_fact_referenced_module_names(atomic_fact);
        for module_name in module_names.iter() {
            let mut arg_shape_keys = self
                .imported_module_environments(module_name)
                .into_iter()
                .filter_map(|env| {
                    env.facts
                        .forall_conclusions
                        .atomic_by_argument_shape
                        .get(&lookup_key)
                })
                .flat_map(|arg_shape_map| arg_shape_map.keys())
                .filter(|key| !arg_shape_lookup_keys.contains(key))
                .cloned()
                .collect::<Vec<_>>();
            let mut seen_arg_shape_keys = Vec::new();
            arg_shape_keys.retain(|key| {
                if seen_arg_shape_keys.contains(key) {
                    return false;
                }
                seen_arg_shape_keys.push(key.clone());
                true
            });
            for arg_shape_key in arg_shape_keys.iter() {
                if let Some(fact_verified) = self
                    .try_verify_with_arg_shape_key_in_imported_module_env(
                        module_name,
                        &lookup_key,
                        arg_shape_key,
                        atomic_fact,
                        verify_state,
                        KnownForallSearchPhase::OtherShape,
                    )?
                {
                    return Ok(Some(fact_verified));
                }
            }
        }
        Ok(None)
    }

    pub(in crate::verification) fn try_verify_with_arg_shape_key_in_env(
        &mut self,
        stack_idx: usize,
        lookup_key: &(AtomicFactKey, bool),
        arg_shape_key: &ForallArgumentShape,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        phase: KnownForallSearchPhase,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let Some(bucket_count) = ({
            let env = self
                .environment_by_top_index(stack_idx)
                .expect("environment index should be valid");
            env.facts
                .forall_conclusions
                .atomic_by_argument_shape
                .get(&lookup_key)
                .and_then(|arg_shape_map| arg_shape_map.get(arg_shape_key))
                .map(|bucket| bucket.len())
        }) else {
            return Ok(None);
        };

        for j in 0..bucket_count {
            let entry_idx = bucket_count - 1 - j;
            let candidate = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                env.facts
                    .forall_conclusions
                    .atomic_by_argument_shape
                    .get(lookup_key)
                    .and_then(|arg_shape_map| arg_shape_map.get(arg_shape_key))
                    .and_then(|bucket| bucket.get(entry_idx))
                    .cloned()
            };
            let Some((atomic_fact_in_known_forall_fact, forall_rc)) = candidate else {
                continue;
            };
            if let Some(fact_verified) = self.try_verify_known_forall_candidate(
                phase,
                atomic_fact_in_known_forall_fact,
                forall_rc,
                atomic_fact,
                verify_state,
            )? {
                return Ok(Some(fact_verified));
            }
        }
        Ok(None)
    }

    pub(in crate::verification) fn try_verify_with_arg_shape_key_in_imported_module_env(
        &mut self,
        module_name: &str,
        lookup_key: &(AtomicFactKey, bool),
        arg_shape_key: &ForallArgumentShape,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        phase: KnownForallSearchPhase,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let module_local_identifiers =
            self.imported_module_identifier_to_local_obj_map(module_name);
        let matching_atomic_fact = self.inst_atomic_fact(
            atomic_fact,
            &module_local_identifiers,
            SubstitutionMode::Named,
            None,
        )?;
        let candidates = self
            .imported_module_environments(module_name)
            .into_iter()
            .filter_map(|env| {
                env.facts
                    .forall_conclusions
                    .atomic_by_argument_shape
                    .get(lookup_key)
                    .and_then(|arg_shape_map| arg_shape_map.get(arg_shape_key))
            })
            .flat_map(|bucket| bucket.iter().rev().cloned())
            .collect::<Vec<_>>();

        for (atomic_fact_in_known_forall_fact, forall_rc) in candidates {
            if let Some(fact_verified) = self.try_verify_known_forall_candidate_with_matching_fact(
                phase,
                atomic_fact_in_known_forall_fact,
                forall_rc,
                &matching_atomic_fact,
                atomic_fact,
                verify_state,
            )? {
                return Ok(Some(fact_verified));
            }
        }
        Ok(None)
    }

    pub(in crate::verification) fn imported_module_identifier_to_local_obj_map(
        &self,
        module_name: &str,
    ) -> HashMap<String, Obj> {
        let mut identifiers = HashMap::new();
        for environment in self.imported_module_environments(module_name) {
            for (name, definition) in environment.definitions.object_symbols() {
                insert_symbol_substitution(
                    &mut identifiers,
                    definition.binding(),
                    IdentifierWithMod::new_bound(
                        module_name.to_string(),
                        name.clone(),
                        definition.binding().as_ref(),
                    )
                    .into(),
                );
            }
        }
        identifiers
    }

    pub fn verify_args_satisfy_forall_requirements(
        &mut self,
        _atomic_fact_in_known_forall_fact: &AtomicFact,
        known_forall: &Rc<StoredForallConclusionReference>,
        mut arg_map: HashMap<String, Obj>,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        self.complete_known_forall_arg_map_from_known_dom_facts(
            known_forall.as_ref(),
            &mut arg_map,
        )?;
        let Some((instantiation, requirements)) = self
            .verify_known_forall_requirements_and_build_evidence(
                known_forall.as_ref(),
                &arg_map,
                given_atomic_fact.clone().into(),
                verify_state,
            )?
        else {
            return Ok(None);
        };

        let source_fact = known_forall.source_fact();
        let source_fact_id = known_forall.source_fact_id;
        let fact_verified = SuccessProveFactResult::new_with_verified_by_known_fact(
            given_atomic_fact.clone().into(),
            SuccessFactProofResult::known_forall_instantiation(
                source_fact,
                source_fact_id,
                known_forall.conclusion_location,
                instantiation,
                requirements,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }

    pub(in crate::verification) fn complete_known_forall_arg_map_from_known_dom_facts(
        &mut self,
        known_forall: &StoredForallConclusionReference,
        arg_map: &mut HashMap<String, Obj>,
    ) -> Result<(), RuntimeError> {
        let param_names = known_forall.params_def.collect_param_names();
        for _ in 0..param_names.len() {
            if param_names
                .iter()
                .all(|param_name| arg_map.contains_key(param_name))
            {
                return Ok(());
            }

            let mut changed = false;
            for dom_fact in known_forall.dom.iter() {
                let Fact::AtomicFact(dom_atomic_fact) = dom_fact else {
                    continue;
                };
                let candidates =
                    self.known_atomic_fact_candidates_for_forall_dom_fact(dom_atomic_fact);
                for candidate in candidates {
                    let Some(candidate_arg_map) = self
                        .match_atomic_fact_args_against_known_forall_ordered_args(
                            dom_atomic_fact,
                            &candidate,
                            &known_forall.params_def,
                        )?
                    else {
                        continue;
                    };
                    let mut merged = arg_map.clone();
                    if !self.merge_arg_match_map_into(&mut merged, candidate_arg_map) {
                        continue;
                    }
                    if merged.len() > arg_map.len() {
                        *arg_map = merged;
                        changed = true;
                        break;
                    }
                }
                if changed {
                    break;
                }
            }

            if !changed {
                return Ok(());
            }
        }
        Ok(())
    }

    pub(in crate::verification) fn known_atomic_fact_candidates_for_forall_dom_fact(
        &self,
        dom_atomic_fact: &AtomicFact,
    ) -> Vec<AtomicFact> {
        let lookup_key = (
            dom_atomic_fact.key(),
            dom_atomic_fact.has_positive_polarity(),
        );
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            match dom_atomic_fact.number_of_args() {
                1 => {
                    if let Some(known_facts) = environment.facts.atomic.by_one_arg.get(&lookup_key)
                    {
                        candidates.extend(known_facts.values().cloned());
                    }
                }
                2 => {
                    if let Some(known_facts) = environment.facts.atomic.by_two_args.get(&lookup_key)
                    {
                        candidates.extend(known_facts.values().cloned());
                    }
                }
                _ => {
                    if let Some(known_facts) =
                        environment.facts.atomic.by_other_arg_count.get(&lookup_key)
                    {
                        candidates.extend(known_facts.iter().cloned());
                    }
                }
            }
        }
        candidates
    }

    pub fn match_atomic_fact_args_against_known_forall_ordered_args(
        &mut self,
        atomic_fact_in_known_forall: &AtomicFact,
        given_fact: &AtomicFact,
        known_forall_params: &TypedParameterList,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut matcher = ArgMatcher::new(
            self,
            arg_match_bindings_for_params(known_forall_params, None),
        );
        let result = matcher.match_atomic_fact_args_in_active_binding_scope(
            atomic_fact_in_known_forall,
            given_fact,
        );
        let Some(raw_arg_map) = result? else {
            return Ok(None);
        };
        Ok(Some(arg_match_map_for_params(
            &raw_arg_map,
            known_forall_params,
        )))
    }

    pub fn match_args_in_fact_with_known_forall_bindings(
        &mut self,
        fact_args_in_known_forall: &[&Obj],
        given_fact_args: &[&Obj],
        known_forall_params: &TypedParameterList,
        known_exist_params: Option<&TypedParameterList>,
    ) -> Result<Option<(HashMap<String, Obj>, HashMap<String, Obj>)>, RuntimeError> {
        let mut matcher = ArgMatcher::new(
            self,
            arg_match_bindings_for_params(known_forall_params, known_exist_params),
        );
        let result =
            matcher.match_args_in_active_binding_scope(fact_args_in_known_forall, given_fact_args);
        let Some(raw_arg_map) = result? else {
            return Ok(None);
        };
        let forall_arg_map = arg_match_map_for_params(&raw_arg_map, known_forall_params);
        let exist_arg_map = known_exist_params
            .map(|params| arg_match_map_for_params(&raw_arg_map, params))
            .unwrap_or_default();
        Ok(Some((forall_arg_map, exist_arg_map)))
    }

    /// Merge `from` into `into`. Returns `false` when a key is already bound to a different object.
    pub(in crate::verification) fn merge_arg_match_map_into(
        &mut self,
        into: &mut HashMap<String, Obj>,
        from: HashMap<String, Obj>,
    ) -> bool {
        for (k, v) in from {
            if let Some(existing) = into.get(&k) {
                if obj_equality_key(existing) != obj_equality_key(&v)
                    && !existing.two_objs_can_be_calculated_and_equal_by_calculation(&v)
                {
                    return false;
                }
            }
            into.insert(k, v);
        }
        true
    }
}
