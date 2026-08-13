use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub(crate) fn contextual_rewrite_diagnostic_for_fact(&mut self, fact: &Fact) -> Vec<String> {
        let Fact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = fact else {
            return Vec::new();
        };

        for side in [&equal_fact.left, &equal_fact.right] {
            let Obj::FnObj(application) = side else {
                continue;
            };
            let total_arguments = application.body.iter().map(Vec::len).sum::<usize>();
            if total_arguments < 2 {
                continue;
            }

            let mut prefix_candidates = Vec::new();
            for group_index in 0..application.body.len() {
                let group = &application.body[group_index];
                for argument_count in 1..=group.len() {
                    let mut prefix_body = application.body[..group_index].to_vec();
                    prefix_body.push(group[..argument_count].to_vec());
                    let used_arguments = prefix_body.iter().map(Vec::len).sum::<usize>();
                    if used_arguments < total_arguments {
                        prefix_candidates.push((prefix_body, total_arguments - used_arguments));
                    }
                }
            }

            for (prefix_body, remaining_arguments) in prefix_candidates.into_iter().rev() {
                let prefix: Obj = FnObj {
                    head: application.head.clone(),
                    body: prefix_body,
                    source_occurrence_id: application.source_occurrence_id,
                }
                .into();
                let representative = self
                    .get_all_obj_representatives_equal_to_given(&prefix)
                    .into_iter()
                    .next()
                    .or_else(|| {
                        self.unfold_known_fn_application_once(
                            &prefix,
                            &UseContextVerifyState::new(0, true),
                        )
                        .ok()
                        .flatten()
                    });
                let Some(representative) = representative else {
                    continue;
                };
                return vec![
                    format!("unmatched outer head: function application {}", side),
                    format!(
                        "nearest known equal operand: {} = {}",
                        prefix, representative
                    ),
                    format!(
                        "the known equality stops before {} remaining argument(s); project or rewrite the prefix before applying them",
                        remaining_arguments
                    ),
                ];
            }
        }

        Vec::new()
    }

    pub(crate) fn verify_non_equational_known_then_builtin_rules_only(
        &mut self,
        atomic_fact: &AtomicFact,
        _verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(atomic_fact)
    }

    /// If the fact string is in the known-facts cache, return the cached verification result.
    pub fn verify_fact_from_cache_using_display_string(&self, fact: &Fact) -> Option<StmtResult> {
        let key = fact.to_string();
        let normalized_key = nested_obj_binder_normalized_fact_key(fact);
        let cached_fact = self.cached_known_fact(&key);
        let cached_fact = if cached_fact.is_some() || normalized_key == key {
            cached_fact
        } else {
            self.cached_known_fact(&normalized_key)
        };
        cached_fact.map(|cached_fact| {
            FactualStmtSuccess::new_with_verified_by_known_fact(
                fact.clone(),
                VerifiedByResult::cached_fact(
                    fact.clone(),
                    cached_fact.line_file.clone(),
                    cached_fact.fact_id,
                ),
                Vec::new(),
            )
            .into()
        })
    }

    /// If check_type_nonempty is true and param_type is Obj(set), verifies that the set is nonempty and stores the fact.
    pub fn verify_param_type_nonempty_if_required(
        &mut self,
        param_type: &ParamType,
        check_type_nonempty: bool,
    ) -> Result<(), RuntimeError> {
        if !check_type_nonempty {
            return Ok(());
        }
        match param_type {
            ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(param_set) => match param_set {
                Obj::FnSet(fn_set) => {
                    let ret_nonempty = IsNonemptySetFact::new(
                        fn_set.body.ret_set.as_ref().clone(),
                        default_line_file(),
                    )
                    .into();
                    self.store_fact_with_well_defined_verification_and_infer(
                        ret_nonempty,
                        &UseContextVerifyState::new(2, false),
                    )?;
                    Ok(())
                }
                Obj::AnonymousFn(anon) => {
                    let ret_nonempty = IsNonemptySetFact::new(
                        anon.body.ret_set.as_ref().clone(),
                        default_line_file(),
                    )
                    .into();
                    self.store_fact_with_well_defined_verification_and_infer(
                        ret_nonempty,
                        &UseContextVerifyState::new(2, false),
                    )?;
                    Ok(())
                }
                _ => {
                    let nonempty_fact =
                        IsNonemptySetFact::new(param_set.clone(), default_line_file());
                    let ret = self.verify_fact_full(
                        &nonempty_fact.into(),
                        &UseContextVerifyState::new(0, false),
                    )?;
                    if ret.is_unknown() {
                        return Err(RuntimeError::from(VerifyRuntimeError(
                            RuntimeErrorStruct::new_with_just_msg(
                                "param type is not nonempty".to_string(),
                            ),
                        )));
                    }
                    Ok(())
                }
            },
        }
    }

    /// Restricted verification mode for builtin premises and well-definedness
    /// side checks.
    ///
    /// This mode may use cached known facts and builtin-only checks. It must not
    /// invoke the full verifier features such as known forall instantiation,
    /// user strategies, or definition expansion.
    pub(crate) fn verify_atomic_fact_restricted_known_builtin(
        &mut self,
        atomic_fact: &AtomicFact,
        _verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&atomic_fact.clone().into())
        {
            return Ok(cached_result);
        }
        self.verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(atomic_fact)
    }

    pub(crate) fn verify_atomic_fact_by_known_atomic_or_builtin_only(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_atomic_fact_restricted_known_builtin(atomic_fact, verify_state)
    }

    pub(crate) fn verify_atomic_fact_known_then_builtin_rules_only(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_atomic_fact_restricted_known_builtin(atomic_fact, verify_state)
    }

    pub(crate) fn verify_quantifier_free_fact_restricted_known_builtin(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            QuantifierFreeFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact_restricted_known_builtin(atomic_fact, verify_state)
            }
            QuantifierFreeFact::AndFact(and_fact) => {
                self.verify_and_fact_known_then_builtin_rules_only(and_fact, verify_state)
            }
            QuantifierFreeFact::ChainFact(chain_fact) => {
                self.verify_chain_fact_known_then_builtin_rules_only(chain_fact, verify_state)
            }
            QuantifierFreeFact::OrFact(or_fact) => {
                self.verify_or_fact_known_then_builtin_rules_only(or_fact, verify_state)
            }
        }
    }

    pub(crate) fn verify_quantifier_free_fact_by_known_atomic_or_builtin_only(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_quantifier_free_fact_restricted_known_builtin(fact, verify_state)
    }

    pub(crate) fn verify_and_chain_atomic_fact_restricted_known_builtin(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact_restricted_known_builtin(atomic_fact, verify_state)
            }
            AndChainAtomicFact::AndFact(and_fact) => {
                self.verify_and_fact_known_then_builtin_rules_only(and_fact, verify_state)
            }
            AndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact_known_then_builtin_rules_only(chain_fact, verify_state)
            }
        }
    }

    pub(crate) fn verify_and_chain_atomic_fact_known_then_builtin_rules_only(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_and_chain_atomic_fact_restricted_known_builtin(fact, verify_state)
    }

    pub(crate) fn verify_and_fact_known_then_builtin_rules_only(
        &mut self,
        and_fact: &AndFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let mut steps = Vec::with_capacity(and_fact.facts.len());
        for atomic_fact in and_fact.facts.iter() {
            let result =
                self.verify_atomic_fact_known_then_builtin_rules_only(atomic_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }
            steps.push(result);
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                and_fact.clone().into(),
                "restricted builtin premise: each conjunct verified".to_string(),
                steps,
            )
            .into(),
        )
    }

    pub(crate) fn verify_chain_fact_known_then_builtin_rules_only(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let facts = chain_fact.facts()?;
        let and_fact = AndFact::new(facts, chain_fact.line_file.clone());
        self.verify_and_fact_known_then_builtin_rules_only(&and_fact, verify_state)
    }

    pub(crate) fn verify_or_fact_known_then_builtin_rules_only(
        &mut self,
        or_fact: &OrFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&or_fact.clone().into())
        {
            return Ok(cached_result);
        }
        let known_or_result = self.verify_or_fact_with_known_or_facts(or_fact)?;
        if known_or_result.is_true() {
            return Ok(known_or_result);
        }
        for fact in or_fact.facts.iter() {
            let result = self
                .verify_and_chain_atomic_fact_known_then_builtin_rules_only(fact, verify_state)?;
            if result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        or_fact.clone().into(),
                        "restricted builtin premise: one branch verified".to_string(),
                        vec![result],
                    )
                    .into(),
                );
            }
        }
        Ok(StmtUnknown::new().into())
    }

    pub(crate) fn verify_known_forall_requirements_and_build_evidence(
        &mut self,
        known_forall: &KnownForallFactParamsAndDom,
        arg_map: &HashMap<String, Obj>,
        goal: Fact,
        verify_state: &UseContextVerifyState,
    ) -> Result<
        Option<(
            Vec<KnownForallInstantiationItem>,
            Vec<KnownForallRequirementResult>,
        )>,
        RuntimeError,
    > {
        let param_names = known_forall.params_def.collect_param_names();
        if !param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        let mut args_for_params: Vec<Obj> = Vec::new();
        for param_name in param_names.iter() {
            let Some(obj) = arg_map.get(param_name) else {
                return Ok(None);
            };
            args_for_params.push(obj.clone());
        }

        let mut requirements = Vec::new();
        if !self.verify_known_forall_param_type_requirements(
            known_forall,
            &args_for_params,
            &goal,
            verify_state,
            &mut requirements,
        )? {
            return Ok(None);
        }

        let param_to_arg_map = match known_forall.params_def.param_def_params_to_arg_map(arg_map) {
            Some(m) => m,
            None => return Ok(None),
        };

        for dom_fact in known_forall.dom.iter() {
            let instantiated_dom_fact = self
                .inst_fact(dom_fact, &param_to_arg_map, ParamObjType::Forall, None)
                .map_err(|e| known_forall_requirement_error(goal.clone(), e))?;
            let result = self
                .verify_fact_full(&instantiated_dom_fact, verify_state)
                .map_err(|e| known_forall_requirement_error(goal.clone(), e))?;
            if result.is_unknown() {
                return Ok(None);
            }
            requirements.push(KnownForallRequirementResult::new(
                instantiated_dom_fact,
                result,
                KnownForallRequirementKind::Domain,
            ));
        }

        let instantiation = param_names
            .iter()
            .zip(args_for_params.iter())
            .map(|(param, arg)| KnownForallInstantiationItem::new(param.clone(), arg.clone()))
            .collect::<Vec<_>>();

        Ok(Some((instantiation, requirements)))
    }

    fn verify_known_forall_param_type_requirements(
        &mut self,
        known_forall: &KnownForallFactParamsAndDom,
        args_for_params: &Vec<Obj>,
        goal: &Fact,
        verify_state: &UseContextVerifyState,
        requirements: &mut Vec<KnownForallRequirementResult>,
    ) -> Result<bool, RuntimeError> {
        // A matcher may synthesize a forall argument while solving an
        // arithmetic pattern, so verify every resulting argument before
        // checking its parameter carrier and domain requirements.
        for arg in args_for_params.iter() {
            if self
                .verify_obj_well_defined_and_store_cache(arg, verify_state)
                .is_err()
            {
                return Ok(false);
            }
        }

        let instantiated_types = self
            .inst_param_def_with_type_one_by_one(
                &known_forall.params_def,
                args_for_params,
                ParamObjType::Forall,
            )
            .map_err(|e| known_forall_requirement_error(goal.clone(), e))?;
        let flat_types = known_forall
            .params_def
            .flat_instantiated_types_for_args(&instantiated_types);
        for (arg, param_type) in args_for_params.iter().zip(flat_types.iter()) {
            let requirement_fact =
                fact_for_param_type_requirement(arg.clone(), param_type, default_line_file());
            let result = self
                .verify_obj_satisfies_param_type(arg.clone(), param_type, verify_state)
                .map_err(|e| known_forall_requirement_error(goal.clone(), e))?;
            if result.is_unknown() {
                return Ok(false);
            }
            requirements.push(KnownForallRequirementResult::new(
                requirement_fact,
                result,
                KnownForallRequirementKind::ParameterType,
            ));
        }
        Ok(true)
    }
}

pub(crate) fn nested_obj_binder_normalized_fact_key(fact: &Fact) -> String {
    let text = fact.to_string();
    match fact {
        Fact::AtomicFact(fact) => {
            nested_obj_binder_normalized_key(&text, fact.get_args_from_fact_ref())
        }
        Fact::ExistFact(fact) => {
            nested_obj_binder_normalized_key(&text, fact.get_args_from_fact_ref())
        }
        Fact::OrFact(fact) => {
            nested_obj_binder_normalized_key(&text, fact.get_args_from_fact_ref())
        }
        Fact::AndFact(fact) => {
            nested_obj_binder_normalized_key(&text, fact.get_args_from_fact_ref())
        }
        Fact::ChainFact(fact) => {
            nested_obj_binder_normalized_key(&text, fact.get_args_from_fact_ref())
        }
        Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => text,
    }
}

fn fact_for_param_type_requirement(obj: Obj, param_type: &ParamType, line_file: LineFile) -> Fact {
    match param_type {
        ParamType::Obj(set_obj) => InFact::new(obj, set_obj.clone(), line_file).into(),
        ParamType::Set(_) => IsSetFact::new(obj, line_file).into(),
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(obj, line_file).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(obj, line_file).into(),
    }
}

fn known_forall_requirement_error(goal: Fact, cause: RuntimeError) -> RuntimeError {
    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
        Some(goal.clone().into_stmt()),
        String::new(),
        goal.line_file(),
        Some(cause),
        vec![],
    )))
}

impl Runtime {
    /// Checks that every operand has a known real carrier before a real-order
    /// builtin rule uses its totality or witness property. A direct `x $in R`
    /// fact is preferred; a known membership in a standard numeric subcarrier
    /// such as `N` also suffices.
    pub(crate) fn verify_objects_are_known_reals(
        &mut self,
        objs: &[&Obj],
        line_file: &LineFile,
        _verify_state: &UseContextVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut seen = Vec::new();
        let mut steps = Vec::new();
        for obj in objs {
            let key = obj.to_string();
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);
            let in_r: AtomicFact =
                InFact::new((*obj).clone(), StandardSet::R.into(), line_file.clone()).into();
            let mut result =
                self.verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(&in_r)?;
            if !result.is_true() {
                result = self.verify_atomic_fact_with_builtin_strategy(&in_r)?;
            }
            if result.is_true() {
                steps.push(result);
                continue;
            }

            // A bound parameter can have a local carrier such as `union(A, B)`.
            // Use only already-known membership and subset facts to lift that
            // carrier into a standard numeric set; do not recursively invoke
            // the general forall engine from a foundational carrier check.
            let mut found_numeric_subcarrier = false;
            for source_set in self.known_sets_containing_obj(obj) {
                let source_membership: AtomicFact =
                    InFact::new((*obj).clone(), source_set.clone(), line_file.clone()).into();
                let source_membership_result = self
                    .verify_non_equational_atomic_fact_with_known_atomic_facts(
                        &source_membership,
                    )?;
                if !source_membership_result.is_true() {
                    continue;
                }

                for carrier in [
                    StandardSet::R,
                    StandardSet::NPos,
                    StandardSet::N,
                    StandardSet::ZNeg,
                    StandardSet::ZStar,
                    StandardSet::Z,
                    StandardSet::Q,
                    StandardSet::QPos,
                    StandardSet::QNeg,
                    StandardSet::QStar,
                    StandardSet::RPos,
                    StandardSet::RNeg,
                    StandardSet::RStar,
                ] {
                    let subset: AtomicFact =
                        SubsetFact::new(source_set.clone(), carrier.into(), line_file.clone())
                            .into();
                    let subset_result =
                        self.verify_non_equational_atomic_fact_with_known_atomic_facts(&subset)?;
                    if !subset_result.is_true() {
                        continue;
                    }
                    steps.push(source_membership_result);
                    steps.push(subset_result);
                    found_numeric_subcarrier = true;
                    break;
                }
                if found_numeric_subcarrier {
                    break;
                }
            }
            if !found_numeric_subcarrier {
                return Ok(None);
            }
        }
        Ok(Some(steps))
    }

    pub(crate) fn known_sets_containing_obj(&self, obj: &Obj) -> Vec<Obj> {
        // This is an index of materialized facts, not the proof closure for
        // `obj`. A proof rule must not use this history to replace a finite
        // target-driven premise search; cache warmth cannot change semantics.
        let probe: AtomicFact = InFact::new(obj.clone(), obj.clone(), default_line_file()).into();
        let module_names = self.atomic_fact_referenced_module_names(&probe);
        let obj_strings = self.all_objs_equal_to_arg_for_known_atomic_fact(obj, &module_names);
        let mut sets = Vec::new();
        let mut seen = std::collections::HashSet::new();

        for environment in self.iter_environments_from_top() {
            Self::collect_known_sets_containing_obj_in_environment(
                environment,
                &obj_strings,
                &mut sets,
                &mut seen,
            );
        }
        for module_name in module_names.iter() {
            for environment in self.imported_module_environments(module_name) {
                Self::collect_known_sets_containing_obj_in_environment(
                    environment,
                    &obj_strings,
                    &mut sets,
                    &mut seen,
                );
            }
        }

        sets
    }

    fn collect_known_sets_containing_obj_in_environment(
        environment: &Environment,
        obj_strings: &[String],
        sets: &mut Vec<Obj>,
        seen: &mut std::collections::HashSet<String>,
    ) {
        for obj_string in obj_strings {
            let Some(owner_sets) = environment.known_owner_sets.get(obj_string) else {
                continue;
            };
            for in_fact in owner_sets.values() {
                let set_string = in_fact.set.to_string();
                if seen.insert(set_string) {
                    sets.push(in_fact.set.clone());
                }
            }
        }
    }
}
