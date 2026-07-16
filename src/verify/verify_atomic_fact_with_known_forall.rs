use crate::prelude::*;
use crate::verify::known_forall_profile::{self, KnownForallSearchPhase};
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

impl Runtime {
    pub fn verify_atomic_fact_with_known_forall(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        known_forall_profile::record_entry();
        if let Some(fact_verified) =
            self.try_verify_with_known_forall_facts_in_envs(atomic_fact, verify_state)?
        {
            known_forall_profile::record_success();
            return Ok((fact_verified).into());
        }

        if let AtomicFact::EqualFact(equal_fact) = atomic_fact {
            let fact_with_reversed_args = EqualFact::new(
                equal_fact.right.clone(),
                equal_fact.left.clone(),
                equal_fact.line_file.clone(),
            );
            let fact_with_reversed_args: AtomicFact = fact_with_reversed_args.into();
            if let Some(fact_verified) = self.try_verify_with_known_forall_facts_in_envs(
                &fact_with_reversed_args,
                verify_state,
            )? {
                known_forall_profile::record_success();
                return Ok((fact_verified).into());
            }

            known_forall_profile::record_unknown();
            return Ok((StmtUnknown::new()).into());
        }

        known_forall_profile::record_unknown();
        Ok((StmtUnknown::new()).into())
    }

    fn get_matched_atomic_fact_in_fallback_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_fact: &AtomicFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        RuntimeError,
    > {
        let key = given_fact.key();
        let is_true = given_fact.is_true();

        let envs_count = self.environment_count();
        let lookup_key = (key.clone(), is_true);
        for i in iterate_from_env_index..envs_count {
            let stack_idx = i;
            let known_forall_facts_count = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                match env.known_atomic_facts_in_forall_facts.get(&lookup_key) {
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
                    let Some(known_forall_facts_in_env) =
                        env.known_atomic_facts_in_forall_facts.get(&lookup_key)
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
                )?;
                if let Some(arg_map) = match_result {
                    known_forall_profile::record_arg_match();
                    return Ok(((i, j), Some(arg_map), Some(current_known_forall)));
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    fn try_verify_with_fallback_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
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

    fn try_verify_with_fallback_known_forall_facts_in_imported_modules(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        module_names: &[String],
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.is_true());
        for module_name in module_names.iter() {
            let module_local_identifiers =
                self.imported_module_identifier_to_local_obj_map(module_name);
            let matching_atomic_fact = self.inst_atomic_fact(
                atomic_fact,
                &module_local_identifiers,
                ParamObjType::Forall,
                None,
            )?;
            let candidates = self
                .imported_module_environments(module_name)
                .into_iter()
                .filter_map(|env| env.known_atomic_facts_in_forall_facts.get(&lookup_key))
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

    fn try_verify_with_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
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

    fn try_verify_known_forall_candidate(
        &mut self,
        phase: KnownForallSearchPhase,
        atomic_fact_in_known_forall_fact: AtomicFact,
        forall_rc: Rc<KnownForallFactParamsAndDom>,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        self.try_verify_known_forall_candidate_with_matching_fact(
            phase,
            atomic_fact_in_known_forall_fact,
            forall_rc,
            given_atomic_fact,
            given_atomic_fact,
            verify_state,
        )
    }

    fn try_verify_known_forall_candidate_with_matching_fact(
        &mut self,
        phase: KnownForallSearchPhase,
        atomic_fact_in_known_forall_fact: AtomicFact,
        forall_rc: Rc<KnownForallFactParamsAndDom>,
        matching_atomic_fact: &AtomicFact,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        known_forall_profile::record_candidate_attempt(phase);
        let match_result = self.match_atomic_fact_args_against_known_forall_ordered_args(
            &atomic_fact_in_known_forall_fact,
            matching_atomic_fact,
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

    fn try_verify_with_arg_shape_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        arg_shape_lookup_keys: &[AtomicFactInForallArgShapeKey],
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.is_true());
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

    fn try_verify_with_other_arg_shape_known_forall_facts_in_envs(
        &mut self,
        atomic_fact: &AtomicFact,
        arg_shape_lookup_keys: &[AtomicFactInForallArgShapeKey],
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let lookup_key = (atomic_fact.key(), atomic_fact.is_true());
        let envs_count = self.environment_count();
        for stack_idx in 0..envs_count {
            let arg_shape_keys = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                let Some(arg_shape_map) = env
                    .known_atomic_facts_in_forall_facts_by_arg_shape
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
                    env.known_atomic_facts_in_forall_facts_by_arg_shape
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

    fn try_verify_with_arg_shape_key_in_env(
        &mut self,
        stack_idx: usize,
        lookup_key: &(AtomicFactKey, bool),
        arg_shape_key: &AtomicFactInForallArgShapeKey,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        phase: KnownForallSearchPhase,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let Some(bucket_count) = ({
            let env = self
                .environment_by_top_index(stack_idx)
                .expect("environment index should be valid");
            env.known_atomic_facts_in_forall_facts_by_arg_shape
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
                env.known_atomic_facts_in_forall_facts_by_arg_shape
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

    fn try_verify_with_arg_shape_key_in_imported_module_env(
        &mut self,
        module_name: &str,
        lookup_key: &(AtomicFactKey, bool),
        arg_shape_key: &AtomicFactInForallArgShapeKey,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        phase: KnownForallSearchPhase,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let module_local_identifiers =
            self.imported_module_identifier_to_local_obj_map(module_name);
        let matching_atomic_fact = self.inst_atomic_fact(
            atomic_fact,
            &module_local_identifiers,
            ParamObjType::Forall,
            None,
        )?;
        let candidates = self
            .imported_module_environments(module_name)
            .into_iter()
            .filter_map(|env| {
                env.known_atomic_facts_in_forall_facts_by_arg_shape
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

    fn imported_module_identifier_to_local_obj_map(
        &self,
        module_name: &str,
    ) -> HashMap<String, Obj> {
        let mut identifiers = HashMap::new();
        for environment in self.imported_module_environments(module_name) {
            for name in environment.defined_identifiers.keys() {
                identifiers.insert(
                    format!("{}{}{}", module_name, MOD_SIGN, name),
                    IdentifierWithMod::new(module_name.to_string(), name.clone()).into(),
                );
            }
        }
        identifiers
    }

    fn verify_args_satisfy_forall_requirements(
        &mut self,
        atomic_fact_in_known_forall_fact: &AtomicFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        mut arg_map: HashMap<String, Obj>,
        given_atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
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

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![atomic_fact_in_known_forall_fact.clone().into()],
            known_forall.line_file.clone(),
        )?;
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact(
            given_atomic_fact.clone().into(),
            VerifiedByResult::known_forall_instantiation(
                verified_by_known_forall_fact.clone().into(),
                instantiation,
                requirements,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }

    fn complete_known_forall_arg_map_from_known_dom_facts(
        &mut self,
        known_forall: &KnownForallFactParamsAndDom,
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

    fn known_atomic_fact_candidates_for_forall_dom_fact(
        &self,
        dom_atomic_fact: &AtomicFact,
    ) -> Vec<AtomicFact> {
        let lookup_key = (dom_atomic_fact.key(), dom_atomic_fact.is_true());
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            match dom_atomic_fact.number_of_args() {
                1 => {
                    if let Some(known_facts) =
                        environment.known_atomic_facts_with_1_arg.get(&lookup_key)
                    {
                        candidates.extend(known_facts.values().cloned());
                    }
                }
                2 => {
                    if let Some(known_facts) =
                        environment.known_atomic_facts_with_2_args.get(&lookup_key)
                    {
                        candidates.extend(known_facts.values().cloned());
                    }
                }
                _ => {
                    if let Some(known_facts) = environment
                        .known_atomic_facts_with_0_or_more_than_2_args
                        .get(&lookup_key)
                    {
                        candidates.extend(known_facts.iter().cloned());
                    }
                }
            }
        }
        candidates
    }

    fn match_atomic_fact_args_against_known_forall_ordered_args(
        &mut self,
        atomic_fact_in_known_forall: &AtomicFact,
        given_fact: &AtomicFact,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if let Some(match_result) =
            self.match_in_fact_standard_set_target(atomic_fact_in_known_forall, given_fact)?
        {
            return Ok(match_result);
        }

        let atomic_fact_args_in_known_forall = atomic_fact_in_known_forall.args_ref();
        let given_args = given_fact.args_ref();
        let forward = self.match_args_in_fact_in_known_forall_fact_with_given_args(
            &atomic_fact_args_in_known_forall,
            &given_args,
        )?;
        return Ok(forward);
    }

    fn match_in_fact_standard_set_target(
        &mut self,
        atomic_fact_in_known_forall: &AtomicFact,
        given_fact: &AtomicFact,
    ) -> Result<Option<Option<HashMap<String, Obj>>>, RuntimeError> {
        let (AtomicFact::InFact(known_in), AtomicFact::InFact(given_in)) =
            (atomic_fact_in_known_forall, given_fact)
        else {
            return Ok(None);
        };
        let (Obj::StandardSet(known_set), Obj::StandardSet(given_set)) =
            (&known_in.set, &given_in.set)
        else {
            return Ok(None);
        };

        let Some(element_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            &known_in.element,
            &given_in.element,
        )?
        else {
            return Ok(Some(None));
        };

        // Narrow known membership implies broader target membership directly.
        // Broad known membership may match a narrow target only when the narrow
        // membership is already a known atomic fact, not merely builtin-provable.
        if Self::standard_set_is_subset_eq(known_set, given_set) {
            return Ok(Some(Some(element_map)));
        }
        if Self::standard_set_is_subset_eq(given_set, known_set) {
            let known_only_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(given_fact)?;
            if known_only_result.is_true() {
                return Ok(Some(Some(element_map)));
            }
        }

        Ok(Some(None))
    }

    pub fn match_args_in_fact_in_known_forall_fact_with_given_args(
        &mut self,
        fact_args_in_known_forall: &[&Obj],
        given_fact_args: &[&Obj],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if fact_args_in_known_forall.len() != given_fact_args.len() {
            return Ok(None);
        }

        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (arg_in_atomic_fact_in_known_forall, arg_in_given) in
            fact_args_in_known_forall.iter().zip(given_fact_args.iter())
        {
            let sub_map = match self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                arg_in_atomic_fact_in_known_forall,
                arg_in_given,
            )? {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }

        Ok(Some(merged))
    }

    // Return None if the given arg does not match the known arg.
    // Return Some(HashMap::new()) if the given arg matches the known arg.
    fn match_arg_in_atomic_fact_in_known_forall_with_given_arg(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match known_arg {
            // Only `*FreeParamObj` bind; plain identifiers are fixed names.
            Obj::Atom(AtomObj::Identifier(ref id_known)) => {
                match given_arg {
                    Obj::Atom(AtomObj::Identifier(id_given)) if id_known.name == id_given.name => {}
                    Obj::Atom(AtomObj::IdentifierWithMod(id_given))
                        if self.is_current_parse_module(&id_given.mod_name)
                            && id_known.name == id_given.name => {}
                    _ => return Ok(None),
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::IdentifierWithMod(ref id_known)) => {
                self.match_arg_when_left_is_identifier_with_mod(id_known, given_arg)
            }
            Obj::FnObj(ref f) => self.match_arg_when_left_is_fn_obj(f, given_arg),
            Obj::Number(ref left) => self.match_arg_when_left_is_number(left, given_arg),
            Obj::Add(ref a) => self.match_arg_when_left_is_add(&a.left, &a.right, given_arg),
            Obj::MatrixAdd(ref a) => {
                self.match_arg_when_left_is_matrix_add(&a.left, &a.right, given_arg)
            }
            Obj::MatrixSub(ref a) => {
                self.match_arg_when_left_is_matrix_sub(&a.left, &a.right, given_arg)
            }
            Obj::MatrixMul(ref a) => {
                self.match_arg_when_left_is_matrix_mul(&a.left, &a.right, given_arg)
            }
            Obj::MatrixScalarMul(ref a) => {
                self.match_arg_when_left_is_matrix_scalar_mul(&a.scalar, &a.matrix, given_arg)
            }
            Obj::MatrixPow(ref a) => {
                self.match_arg_when_left_is_matrix_pow(&a.base, &a.exponent, given_arg)
            }
            Obj::Sub(ref a) => self.match_arg_when_left_is_sub(&a.left, &a.right, given_arg),
            Obj::Mul(ref a) => self.match_arg_when_left_is_mul(&a.left, &a.right, given_arg),
            Obj::Div(ref a) => self.match_arg_when_left_is_div(&a.left, &a.right, given_arg),
            Obj::Mod(ref a) => self.match_arg_when_left_is_mod(&a.left, &a.right, given_arg),
            Obj::IntegerQuotient(ref a) => {
                self.match_arg_when_left_is_integer_quotient(&a.dividend, &a.divisor, given_arg)
            }
            Obj::Pow(ref a) => self.match_arg_when_left_is_pow(&a.base, &a.exponent, given_arg),
            Obj::Abs(ref a) => self.match_arg_when_left_is_abs(a.arg.as_ref(), given_arg),
            Obj::Sqrt(ref a) => self.match_arg_when_left_is_sqrt(a.arg.as_ref(), given_arg),
            Obj::Log(ref a) => self.match_arg_when_left_is_log(&a.base, &a.arg, given_arg),
            Obj::Max(ref a) => self.match_arg_when_left_is_max(&a.left, &a.right, given_arg),
            Obj::Min(ref a) => self.match_arg_when_left_is_min(&a.left, &a.right, given_arg),
            Obj::Union(ref a) => self.match_arg_when_left_is_union(&a.left, &a.right, given_arg),
            Obj::Intersect(ref a) => {
                self.match_arg_when_left_is_intersect(&a.left, &a.right, given_arg)
            }
            Obj::SetMinus(ref a) => {
                self.match_arg_when_left_is_set_minus(&a.left, &a.right, given_arg)
            }
            Obj::SetDiff(ref a) => {
                self.match_arg_when_left_is_set_diff(&a.left, &a.right, given_arg)
            }
            Obj::Cup(ref a) => self.match_arg_when_left_is_cup(&a.left, given_arg),
            Obj::Cap(ref a) => self.match_arg_when_left_is_cap(&a.left, given_arg),
            Obj::GeneralCart(ref left) => self.match_arg_when_left_is_general_cart(left, given_arg),
            Obj::ListSet(ref left) => self.match_arg_when_left_is_list_set(&left.list, given_arg),
            Obj::SetBuilder(ref left) => self.match_arg_when_left_is_set_builder(left, given_arg),
            Obj::FnSet(ref left) => self.match_arg_when_left_is_fn_set_with_params(left, given_arg),
            Obj::AnonymousFn(ref left) => {
                self.match_arg_when_left_is_anonymous_fn_with_params(left, given_arg)
            }
            Obj::StandardSet(StandardSet::NPos) => self.match_arg_when_left_is_n_pos_obj(given_arg),
            Obj::StandardSet(StandardSet::N) => self.match_arg_when_left_is_n_obj(given_arg),
            Obj::StandardSet(StandardSet::Q) => self.match_arg_when_left_is_q_obj(given_arg),
            Obj::StandardSet(StandardSet::Z) => self.match_arg_when_left_is_z_obj(given_arg),
            Obj::StandardSet(StandardSet::R) => self.match_arg_when_left_is_r_obj(given_arg),
            Obj::Cart(ref left) => self.match_arg_when_left_is_cart(&left.args, given_arg),
            Obj::CartDim(ref left) => {
                self.match_arg_when_left_is_cart_dim(left.set.as_ref(), given_arg)
            }
            Obj::Proj(ref left) => {
                self.match_arg_when_left_is_proj(left.set.as_ref(), left.dim.as_ref(), given_arg)
            }
            Obj::TupleDim(ref left) => {
                self.match_arg_when_left_is_dim(left.arg.as_ref(), given_arg)
            }
            Obj::Tuple(ref left) => self.match_arg_when_left_is_tuple(&left.args, given_arg),
            Obj::FiniteSeqListObj(ref left) => {
                self.match_arg_when_left_is_finite_seq_list(&left.objs, given_arg)
            }
            Obj::FiniteSetSize(ref left) => {
                self.match_arg_when_left_is_finite_set_size(left.set.as_ref(), given_arg)
            }
            Obj::FnRange(ref left) => {
                self.match_arg_when_left_is_fn_range(left.function.as_ref(), given_arg)
            }
            Obj::Replacement(ref left) => self.match_arg_when_left_is_replacement(left, given_arg),
            Obj::Sum(ref left) => self.match_arg_when_left_is_sum(
                left.start.as_ref(),
                left.end.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::SumOfFiniteSet(ref left) => self.match_arg_when_left_is_finite_set_sum(
                left.set.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::Product(ref left) => self.match_arg_when_left_is_product(
                left.start.as_ref(),
                left.end.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::ProductOfFiniteSet(ref left) => self.match_arg_when_left_is_finite_set_product(
                left.set.as_ref(),
                left.func.as_ref(),
                given_arg,
            ),
            Obj::Range(ref left) => {
                self.match_arg_when_left_is_range(left.start.as_ref(), left.end.as_ref(), given_arg)
            }
            Obj::ClosedRange(ref left) => self.match_arg_when_left_is_closed_range(
                left.start.as_ref(),
                left.end.as_ref(),
                given_arg,
            ),
            Obj::IntervalObj(ref left) => self.match_arg_when_left_is_interval(left, given_arg),
            Obj::OneSideInfinityIntervalObj(ref left) => {
                self.match_arg_when_left_is_one_side_infinity_interval(left, given_arg)
            }
            Obj::FiniteSeqSet(ref left) => self.match_arg_when_left_is_finite_seq_set(
                left.set.as_ref(),
                left.n.as_ref(),
                given_arg,
            ),
            Obj::SeqSet(ref left) => {
                self.match_arg_when_left_is_seq_set(left.set.as_ref(), given_arg)
            }
            Obj::MatrixListObj(ref left) => {
                self.match_arg_when_left_is_matrix_list(&left.rows, given_arg)
            }
            Obj::MatrixSet(ref left) => self.match_arg_when_left_is_matrix_set(
                left.set.as_ref(),
                left.row_len.as_ref(),
                left.col_len.as_ref(),
                given_arg,
            ),
            Obj::PowerSet(ref left) => {
                self.match_arg_when_left_is_power_set(left.set.as_ref(), given_arg)
            }
            Obj::ObjAtIndex(ref left) => self.match_arg_when_left_is_obj_at_index(
                left.obj.as_ref(),
                left.index.as_ref(),
                given_arg,
            ),
            Obj::StandardSet(StandardSet::QPos) => self.match_arg_when_left_is_q_pos(given_arg),
            Obj::StandardSet(StandardSet::RPos) => self.match_arg_when_left_is_r_pos(given_arg),
            Obj::StandardSet(StandardSet::QNeg) => self.match_arg_when_left_is_q_neg(given_arg),
            Obj::StandardSet(StandardSet::ZNeg) => self.match_arg_when_left_is_z_neg(given_arg),
            Obj::StandardSet(StandardSet::RNeg) => self.match_arg_when_left_is_r_neg(given_arg),
            Obj::StandardSet(StandardSet::QNz) => self.match_arg_when_left_is_q_nz(given_arg),
            Obj::StandardSet(StandardSet::ZNz) => self.match_arg_when_left_is_z_nz(given_arg),
            Obj::StandardSet(StandardSet::RNz) => self.match_arg_when_left_is_r_nz(given_arg),
            Obj::StructObj(known) => match given_arg {
                Obj::StructObj(given) => {
                    if known.name.to_string() != given.name.to_string() {
                        return Ok(None);
                    }
                    self.match_arg_vec_then_merge(&known.params, &given.params)
                }
                _ => Ok(None),
            },
            Obj::ObjAsStructInstanceWithFieldAccess(known) => match given_arg {
                Obj::ObjAsStructInstanceWithFieldAccess(given) => {
                    if known.struct_obj.name.to_string() != given.struct_obj.name.to_string()
                        || known.field_name != given.field_name
                    {
                        return Ok(None);
                    }
                    let params_result = self.match_arg_vec_then_merge(
                        &known.struct_obj.params,
                        &given.struct_obj.params,
                    )?;
                    let obj_result = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        known.obj.as_ref(),
                        given.obj.as_ref(),
                    )?;
                    match (params_result, obj_result) {
                        (Some(params_map), Some(obj_map)) => {
                            Ok(self.merge_arg_match_maps(params_map, obj_map))
                        }
                        _ => Ok(None),
                    }
                }
                _ => Ok(None),
            },
            Obj::InstantiatedTemplateObj(known) => match given_arg {
                Obj::InstantiatedTemplateObj(given) => {
                    if known.template_name != given.template_name {
                        return Ok(None);
                    }
                    self.match_arg_vec_then_merge(&known.args, &given.args)
                }
                _ => Ok(None),
            },
            Obj::Atom(AtomObj::Forall(ref p)) => {
                self.match_arg_when_left_is_forall_param(p, given_arg)
            }
            Obj::Atom(AtomObj::Def(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::Exist(ref p)) => match given_arg {
                Obj::Atom(AtomObj::Exist(_)) => {
                    let mut m = HashMap::new();
                    m.insert(p.name.clone(), given_arg.clone());
                    Ok(Some(m))
                }
                _ => {
                    if p.to_string() != given_arg.to_string() {
                        return Ok(None);
                    }
                    Ok(Some(HashMap::new()))
                }
            },
            Obj::Atom(AtomObj::SetBuilder(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::FnSet(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::Induc(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::DefAlgo(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::DefStructField(ref p)) => {
                if p.to_string() != given_arg.to_string() {
                    return Ok(None);
                }
                Ok(Some(HashMap::new()))
            }
            Obj::Atom(AtomObj::TupleIndex(ref p)) => {
                let mut map = HashMap::new();
                map.insert(p.name.clone(), given_arg.clone());
                Ok(Some(map))
            }
            Obj::Atom(AtomObj::CartIndex(ref p)) => {
                let mut map = HashMap::new();
                map.insert(p.name.clone(), given_arg.clone());
                Ok(Some(map))
            }
        }
    }

    fn match_arg_when_left_is_forall_param(
        &mut self,
        id_known: &ForallFreeParamObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut map = HashMap::new();
        map.insert(id_known.name.clone(), given_arg.clone());
        Ok(Some(map))
    }

    fn match_arg_when_left_is_identifier_with_mod(
        &mut self,
        id_known: &IdentifierWithMod,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Atom(AtomObj::IdentifierWithMod(id_given)) => {
                if id_known.mod_name == id_given.mod_name && id_known.name == id_given.name {
                    Ok(Some(HashMap::new()))
                } else {
                    Ok(None)
                }
            }
            Obj::Atom(AtomObj::Identifier(id_given))
                if self.is_current_parse_module(&id_known.mod_name)
                    && id_known.name == id_given.name =>
            {
                Ok(Some(HashMap::new()))
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_obj(
        &mut self,
        left: &FnObj,
        right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match right {
            Obj::FnObj(ref right_fn) => {
                // body lengths must match
                if left.body.len() != right_fn.body.len() {
                    return Ok(None);
                }

                let left_head: Obj = left.head.as_ref().clone().into();
                let right_head: Obj = right_fn.head.as_ref().clone().into();

                // heads must match
                let head_match = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    &left_head,
                    &right_head,
                )?;
                let mut head_map = match head_match {
                    Some(m) => m,
                    None => return Ok(None),
                };

                for (left_row, right_row) in left.body.iter().zip(right_fn.body.iter()) {
                    if left_row.len() != right_row.len() {
                        return Ok(None);
                    }
                    for (left_arg, right_arg) in left_row.iter().zip(right_row.iter()) {
                        let sub_map = match self
                            .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                                left_arg.as_ref(),
                                right_arg.as_ref(),
                            )? {
                            Some(m) => m,
                            None => return Ok(None),
                        };
                        if !self.merge_arg_match_map_into(&mut head_map, sub_map) {
                            return Ok(None);
                        }
                    }
                }

                Ok(Some(head_map))
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_number(
        &mut self,
        left: &Number,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if !given_arg.evaluate_to_normalized_decimal_number().is_some() {
            return Ok(None);
        }
        let left_obj: Obj = left.clone().into();
        if left_obj.two_objs_can_be_calculated_and_equal_by_calculation(given_arg) {
            Ok(Some(HashMap::new()))
        } else {
            Ok(None)
        }
    }

    fn match_arg_when_left_is_matrix_add(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixAdd(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_sub(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixSub(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_mul(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixMul(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_scalar_mul(
        &mut self,
        left_scalar: &Obj,
        left_matrix: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixScalarMul(ref g) => {
                self.match_arg_binary_then_merge(left_scalar, left_matrix, &g.scalar, &g.matrix)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_pow(
        &mut self,
        left_base: &Obj,
        left_exp: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixPow(ref g) => {
                self.match_arg_binary_then_merge(left_base, left_exp, &g.base, &g.exponent)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_add(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Add(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(left_left_number) = left_left {
                    let new_given = Sub::new(given_arg.clone(), left_left_number.clone().into());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right,
                        &new_given.into(),
                    );
                } else if let Obj::Number(left_right_number) = left_right {
                    let new_given = Sub::new(given_arg.clone(), left_right_number.clone().into());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    fn match_arg_when_left_is_sub(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sub(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(right_number) = left_right {
                    let new_given = Add::new(right_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else if let Obj::Number(left_left_number) = left_left {
                    let new_given = Sub::new(left_left_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    fn match_arg_when_left_is_mul(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Mul(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                let neg_one: Obj = Number::new("-1".to_string()).into();
                let known_left_is_neg_one = match left_left {
                    Obj::Number(n) => {
                        let left_obj: Obj = n.clone().into();
                        "-1".to_string() == left_obj.to_string()
                    }
                    _ => false,
                };
                if known_left_is_neg_one {
                    let synthetic: Obj = Mul::new(neg_one, given_arg.clone()).into();
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_right, &synthetic,
                    );
                } else {
                    if let Obj::Number(n) = left_left {
                        if n.normalized_value == "0".to_string() {
                            return Ok(None);
                        } else {
                            let synthetic: Obj =
                                Div::new(given_arg.clone(), n.clone().into()).into();
                            return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                                left_right, &synthetic,
                            );
                        }
                    } else if let Obj::Number(left_right_number) = left_right {
                        let new_given =
                            Div::new(given_arg.clone(), left_right_number.clone().into());
                        return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                            left_left,
                            &new_given.into(),
                        );
                    } else {
                        return Ok(None);
                    }
                }
            }
        }
    }

    fn match_arg_when_left_is_div(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Div(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => {
                if let Obj::Number(left_right_number) = left_right {
                    let new_given = Mul::new(left_right_number.clone().into(), given_arg.clone());
                    return self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                        left_left,
                        &new_given.into(),
                    );
                } else {
                    return Ok(None);
                }
            }
        }
    }

    fn match_arg_when_left_is_mod(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Mod(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_integer_quotient(
        &mut self,
        dividend: &Obj,
        divisor: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::IntegerQuotient(given) => {
                self.match_arg_binary_then_merge(dividend, divisor, &given.dividend, &given.divisor)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_pow(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Pow(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.base, &g.exponent)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_abs(
        &mut self,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Abs(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_arg, &g.arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_sqrt(
        &mut self,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sqrt(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_arg, &g.arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_log(
        &mut self,
        left_base: &Obj,
        left_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Log(ref g) => {
                self.match_arg_binary_then_merge(left_base, left_arg, &g.base, &g.arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_max(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Max(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_min(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Min(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_union(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Union(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_intersect(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Intersect(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_minus(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SetMinus(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_set_diff(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SetDiff(ref g) => {
                self.match_arg_binary_then_merge(left_left, left_right, &g.left, &g.right)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cup(
        &mut self,
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Cup(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cap(
        &mut self,
        left_left: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Cap(ref g) => {
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, &g.left)
            }
            _ => Ok(None),
        }
    }

    /// Match two pairs (left_left, given_left) and (left_right, given_right); if either returns None, return None; else merge maps and return Some(merged).
    fn match_arg_binary_then_merge(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let left_res =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_left, given_left)?;
        let map1 = match left_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let right_res =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_right, given_right)?;
        let map2 = match right_res {
            Some(m) => m,
            None => return Ok(None),
        };
        let merged = self.merge_arg_match_maps(map1, map2);
        Ok(merged)
    }

    fn match_arg_ternary_then_merge(
        &mut self,
        a1: &Obj,
        a2: &Obj,
        a3: &Obj,
        b1: &Obj,
        b2: &Obj,
        b3: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let m12 = self.match_arg_binary_then_merge(a1, a2, b1, b2)?;
        let map12 = match m12 {
            Some(m) => m,
            None => return Ok(None),
        };
        let m3 = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(a3, b3)?;
        let map3 = match m3 {
            Some(m) => m,
            None => return Ok(None),
        };
        Ok(self.merge_arg_match_maps(map12, map3))
    }

    /// Merge `from` into `into`. Returns `false` when a key is already bound to a different object.
    fn merge_arg_match_map_into(
        &mut self,
        into: &mut HashMap<String, Obj>,
        from: HashMap<String, Obj>,
    ) -> bool {
        for (k, v) in from {
            if let Some(existing) = into.get(&k) {
                if existing.to_string() != v.to_string()
                    && !existing.two_objs_can_be_calculated_and_equal_by_calculation(&v)
                {
                    return false;
                }
            }
            into.insert(k, v);
        }
        true
    }

    fn merge_arg_match_maps(
        &mut self,
        mut map1: HashMap<String, Obj>,
        map2: HashMap<String, Obj>,
    ) -> Option<HashMap<String, Obj>> {
        if !self.merge_arg_match_map_into(&mut map1, map2) {
            return None;
        }
        Some(map1)
    }

    /// Zip known/given argument pairs of equal length; merge substitution maps from each recursive match.
    fn match_arg_pairs_then_merge(
        &mut self,
        pairs: Vec<(&Obj, &Obj)>,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (left_elem, given_elem) in pairs {
            let sub_map = match self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(left_elem, given_elem)?
            {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_boxed_arg_vec_then_merge(
        &mut self,
        left_elements: &[Box<Obj>],
        given_elements: &[Box<Obj>],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left_elements.len() != given_elements.len() {
            return Ok(None);
        }
        let pairs = left_elements
            .iter()
            .zip(given_elements.iter())
            .map(|(l, g)| (l.as_ref(), g.as_ref()))
            .collect();
        self.match_arg_pairs_then_merge(pairs)
    }

    fn match_arg_vec_then_merge(
        &mut self,
        left: &[Obj],
        given: &[Obj],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.len() != given.len() {
            return Ok(None);
        }
        let pairs = left.iter().zip(given.iter()).collect();
        self.match_arg_pairs_then_merge(pairs)
    }

    fn match_arg_matrix_rows_then_merge(
        &mut self,
        left_rows: &[Vec<Box<Obj>>],
        given_rows: &[Vec<Box<Obj>>],
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left_rows.len() != given_rows.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lr, gr) in left_rows.iter().zip(given_rows.iter()) {
            let sub_map = match self.match_boxed_arg_vec_then_merge(lr, gr)? {
                Some(m) => m,
                None => return Ok(None),
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_when_left_is_list_set(
        &mut self,
        left_list: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ListSet(ref given) => self.match_boxed_arg_vec_then_merge(left_list, &given.list),
            _ => Ok(None),
        }
    }

    fn match_arg_or_and_chain_atomic_fact_in_known_forall(
        &mut self,
        left: &OrAndChainAtomicFact,
        given: &OrAndChainAtomicFact,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if !Self::_verify_or_and_chain_atomic_facts_the_same_type_ref(left, given)? {
            return Ok(None);
        }

        let left_args = left.get_args_from_fact_ref();
        let given_args = given.get_args_from_fact_ref();
        self.match_args_in_fact_in_known_forall_fact_with_given_args(&left_args, &given_args)
    }

    fn match_arg_exist_body_fact_in_known_forall(
        &mut self,
        left: &ExistBodyFact,
        given: &ExistBodyFact,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if !exist_body_facts_have_same_shape(left, given)? {
            return Ok(None);
        }
        let left_args = left.get_args_from_fact_ref();
        let given_args = given.get_args_from_fact_ref();
        self.match_args_in_fact_in_known_forall_fact_with_given_args(&left_args, &given_args)
    }

    fn match_arg_when_left_is_set_builder(
        &mut self,
        left: &SetBuilder,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::SetBuilder(given) = given_arg else {
            return Ok(None);
        };
        if left.param != given.param {
            return Ok(None);
        }
        let Some(mut merged) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.param_set.as_ref(),
            given.param_set.as_ref(),
        )?
        else {
            return Ok(None);
        };
        if left.facts.len() != given.facts.len() {
            return Ok(None);
        }
        for (lf, gf) in left.facts.iter().zip(given.facts.iter()) {
            let Some(fact_map) = self.match_arg_exist_body_fact_in_known_forall(lf, gf)? else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, fact_map) {
                return Ok(None);
            }
        }
        let verify_state = VerifyState::new_with_final_round(false);
        for value in merged.values() {
            if self
                .verify_obj_well_defined_and_store_cache(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_when_left_is_general_cart(
        &mut self,
        left: &GeneralCart,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::GeneralCart(given) = given_arg else {
            return Ok(None);
        };
        self.match_args_in_fact_in_known_forall_fact_with_given_args(
            &[
                left.index_set.as_ref(),
                left.family_set.as_ref(),
                left.family_fn.as_ref(),
            ],
            &[
                given.index_set.as_ref(),
                given.family_set.as_ref(),
                given.family_fn.as_ref(),
            ],
        )
    }

    fn match_arg_when_left_is_fn_set_with_params(
        &mut self,
        left: &FnSet,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::FnSet(given) = given_arg else {
            return Ok(None);
        };
        if left.body.params_def_with_set.len() != given.body.params_def_with_set.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lg, gg) in left
            .body
            .params_def_with_set
            .iter()
            .zip(given.body.params_def_with_set.iter())
        {
            if lg.params != gg.params {
                return Ok(None);
            }
            let Some(m) = self.match_fn_param_group_type_in_known_forall_with_given(lg, gg)? else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, m) {
                return Ok(None);
            }
        }
        if left.body.dom_facts.len() != given.body.dom_facts.len() {
            return Ok(None);
        }
        for (lf, gf) in left.body.dom_facts.iter().zip(given.body.dom_facts.iter()) {
            let Some(fact_map) = self.match_arg_or_and_chain_atomic_fact_in_known_forall(lf, gf)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, fact_map) {
                return Ok(None);
            }
        }
        let Some(ret_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.body.ret_set.as_ref(),
            given.body.ret_set.as_ref(),
        )?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, ret_map) {
            return Ok(None);
        }
        let verify_state = VerifyState::new_with_final_round(false);
        for value in merged.values() {
            if self
                .verify_obj_well_defined_and_store_cache(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_arg_when_left_is_anonymous_fn_with_params(
        &mut self,
        left: &AnonymousFn,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::AnonymousFn(given) = given_arg else {
            return Ok(None);
        };

        let left_param_count = ParamGroupWithSet::number_of_params(&left.body.params_def_with_set);
        let given_param_count =
            ParamGroupWithSet::number_of_params(&given.body.params_def_with_set);
        if left_param_count != given_param_count {
            return Ok(None);
        }

        // Anonymous-function parameter names are binders, not part of the
        // function value.  Rename both sides to the same internal names before
        // matching their domains and bodies.  For example, `fn(k R) R {k}` and
        // `fn(i R) R {i}` must match here.
        let alpha_names = Self::anonymous_fn_alpha_param_names(left_param_count);
        let left = self.anonymous_fn_with_alpha_renamed_params(left, &alpha_names)?;
        let given = self.anonymous_fn_with_alpha_renamed_params(given, &alpha_names)?;
        self.match_alpha_renamed_anonymous_fn_with_params(&left, &given)
    }

    fn match_alpha_renamed_anonymous_fn_with_params(
        &mut self,
        left: &AnonymousFn,
        given: &AnonymousFn,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.body.params_def_with_set.len() != given.body.params_def_with_set.len() {
            return Ok(None);
        }
        let mut merged: HashMap<String, Obj> = HashMap::new();
        for (lg, gg) in left
            .body
            .params_def_with_set
            .iter()
            .zip(given.body.params_def_with_set.iter())
        {
            if lg.params != gg.params {
                return Ok(None);
            }
            let Some(m) = self.match_fn_param_group_type_in_known_forall_with_given(lg, gg)? else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, m) {
                return Ok(None);
            }
        }
        if left.body.dom_facts.len() != given.body.dom_facts.len() {
            return Ok(None);
        }
        for (lf, gf) in left.body.dom_facts.iter().zip(given.body.dom_facts.iter()) {
            let Some(fact_map) = self.match_arg_or_and_chain_atomic_fact_in_known_forall(lf, gf)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, fact_map) {
                return Ok(None);
            }
        }
        let Some(ret_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.body.ret_set.as_ref(),
            given.body.ret_set.as_ref(),
        )?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, ret_map) {
            return Ok(None);
        }
        let Some(eq_map) = self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.equal_to.as_ref(),
            given.equal_to.as_ref(),
        )?
        else {
            let Some(eq_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
                left.equal_to.as_ref(),
                given.equal_to.as_ref(),
                &given.body,
            )?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, eq_map) {
                return Ok(None);
            }
            let verify_state = VerifyState::new_with_final_round(false);
            for value in merged.values() {
                if self
                    .verify_obj_well_defined_and_store_cache(value, &verify_state)
                    .is_err()
                {
                    return Ok(None);
                }
            }
            return Ok(Some(merged));
        };
        if !self.merge_arg_match_map_into(&mut merged, eq_map) {
            return Ok(None);
        }
        let verify_state = VerifyState::new_with_final_round(false);
        for value in merged.values() {
            if self
                .verify_obj_well_defined_and_store_cache(value, &verify_state)
                .is_err()
            {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    pub(crate) fn objs_match_for_fact_lookup(
        &self,
        known_arg: &Obj,
        given_arg: &Obj,
    ) -> Result<bool, RuntimeError> {
        if known_arg.to_string() == given_arg.to_string() {
            return Ok(true);
        }

        let (Obj::AnonymousFn(known), Obj::AnonymousFn(given)) = (known_arg, given_arg) else {
            return Ok(false);
        };
        self.anonymous_fns_are_alpha_equivalent(known, given)
    }

    fn anonymous_fns_are_alpha_equivalent(
        &self,
        left: &AnonymousFn,
        right: &AnonymousFn,
    ) -> Result<bool, RuntimeError> {
        let left_param_count = ParamGroupWithSet::number_of_params(&left.body.params_def_with_set);
        let right_param_count =
            ParamGroupWithSet::number_of_params(&right.body.params_def_with_set);
        if left_param_count != right_param_count {
            return Ok(false);
        }

        let alpha_names = Self::anonymous_fn_alpha_param_names(left_param_count);
        let left = self.anonymous_fn_with_alpha_renamed_params(left, &alpha_names)?;
        let right = self.anonymous_fn_with_alpha_renamed_params(right, &alpha_names)?;
        Ok(left.to_string() == right.to_string())
    }

    fn anonymous_fn_alpha_param_names(param_count: usize) -> Vec<String> {
        (0..param_count)
            .map(|index| format!("#anonymous_fn_alpha_{}", index))
            .collect()
    }

    fn anonymous_fn_with_alpha_renamed_params(
        &self,
        anonymous_fn: &AnonymousFn,
        alpha_names: &[String],
    ) -> Result<AnonymousFn, RuntimeError> {
        let param_names =
            ParamGroupWithSet::collect_param_names(&anonymous_fn.body.params_def_with_set);
        if param_names.len() != alpha_names.len() {
            return Err(VerifyRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                "internal: anonymous-function alpha rename needs one name per parameter"
                    .to_string(),
            ))
            .into());
        }

        let mut param_to_alpha_name = HashMap::with_capacity(param_names.len());
        for (param_name, alpha_name) in param_names.iter().zip(alpha_names.iter()) {
            param_to_alpha_name.insert(
                param_name.clone(),
                obj_for_bound_param_in_scope(alpha_name.clone(), ParamObjType::FnSet),
            );
        }

        let mut params_def_with_set =
            Vec::with_capacity(anonymous_fn.body.params_def_with_set.len());
        let mut next_alpha_name = 0;
        for group in anonymous_fn.body.params_def_with_set.iter() {
            let group_len = group.params.len();
            let params = alpha_names[next_alpha_name..next_alpha_name + group_len].to_vec();
            next_alpha_name += group_len;
            let param_set =
                self.inst_obj(group.set_obj(), &param_to_alpha_name, ParamObjType::FnSet)?;
            params_def_with_set.push(ParamGroupWithSet::new(params, param_set));
        }

        let mut dom_facts = Vec::with_capacity(anonymous_fn.body.dom_facts.len());
        for dom_fact in anonymous_fn.body.dom_facts.iter() {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(
                dom_fact,
                &param_to_alpha_name,
                ParamObjType::FnSet,
                None,
            )?);
        }

        AnonymousFn::new(
            params_def_with_set,
            dom_facts,
            self.inst_obj(
                anonymous_fn.body.ret_set.as_ref(),
                &param_to_alpha_name,
                ParamObjType::FnSet,
            )?,
            self.inst_obj(
                anonymous_fn.equal_to.as_ref(),
                &param_to_alpha_name,
                ParamObjType::FnSet,
            )?,
        )
    }

    fn match_arg_in_anonymous_fn_body_with_given_arg(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if let Some(existing_match) =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(known_arg, given_arg)?
        {
            return Ok(Some(existing_match));
        }
        if let Some(function_param_match) = self
            .match_forall_function_param_application_as_anonymous_fn(
                known_arg,
                given_arg,
                anonymous_fn_body,
            )?
        {
            return Ok(Some(function_param_match));
        }

        match (known_arg, given_arg) {
            (Obj::FnObj(left), Obj::FnObj(given)) => {
                self.match_fn_obj_in_anonymous_fn_body(left, given, anonymous_fn_body)
            }
            (Obj::Add(left), Obj::Add(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Sub(left), Obj::Sub(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Mul(left), Obj::Mul(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Div(left), Obj::Div(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Mod(left), Obj::Mod(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::IntegerQuotient(left), Obj::IntegerQuotient(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.dividend.as_ref(),
                    left.divisor.as_ref(),
                    given.dividend.as_ref(),
                    given.divisor.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Pow(left), Obj::Pow(given)) => self.match_binary_in_anonymous_fn_body(
                left.base.as_ref(),
                left.exponent.as_ref(),
                given.base.as_ref(),
                given.exponent.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::MatrixAdd(left), Obj::MatrixAdd(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixSub(left), Obj::MatrixSub(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixMul(left), Obj::MatrixMul(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixScalarMul(left), Obj::MatrixScalarMul(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.scalar.as_ref(),
                    left.matrix.as_ref(),
                    given.scalar.as_ref(),
                    given.matrix.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixPow(left), Obj::MatrixPow(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.base.as_ref(),
                    left.exponent.as_ref(),
                    given.base.as_ref(),
                    given.exponent.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Abs(left), Obj::Abs(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Sqrt(left), Obj::Sqrt(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Log(left), Obj::Log(given)) => self.match_binary_in_anonymous_fn_body(
                left.base.as_ref(),
                left.arg.as_ref(),
                given.base.as_ref(),
                given.arg.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Max(left), Obj::Max(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Min(left), Obj::Min(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Tuple(left), Obj::Tuple(given)) => self.match_boxed_args_in_anonymous_fn_body(
                &left.args,
                &given.args,
                anonymous_fn_body,
            ),
            (Obj::Cart(left), Obj::Cart(given)) => self.match_boxed_args_in_anonymous_fn_body(
                &left.args,
                &given.args,
                anonymous_fn_body,
            ),
            (Obj::ListSet(left), Obj::ListSet(given)) => self
                .match_boxed_args_in_anonymous_fn_body(&left.list, &given.list, anonymous_fn_body),
            (Obj::FiniteSeqListObj(left), Obj::FiniteSeqListObj(given)) => self
                .match_boxed_args_in_anonymous_fn_body(&left.objs, &given.objs, anonymous_fn_body),
            _ => Ok(None),
        }
    }

    fn match_fn_obj_in_anonymous_fn_body(
        &mut self,
        left: &FnObj,
        given: &FnObj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.body.len() != given.body.len() {
            return Ok(None);
        }
        let left_head: Obj = left.head.as_ref().clone().into();
        let given_head: Obj = given.head.as_ref().clone().into();
        let Some(mut merged) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            &left_head,
            &given_head,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };

        for (left_row, given_row) in left.body.iter().zip(given.body.iter()) {
            if left_row.len() != given_row.len() {
                return Ok(None);
            }
            let Some(row_map) =
                self.match_boxed_args_in_anonymous_fn_body(left_row, given_row, anonymous_fn_body)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, row_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_binary_in_anonymous_fn_body(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Some(mut merged) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            left_left,
            given_left,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };
        let Some(right_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            left_right,
            given_right,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, right_map) {
            return Ok(None);
        }
        Ok(Some(merged))
    }

    fn match_boxed_args_in_anonymous_fn_body(
        &mut self,
        left: &[Box<Obj>],
        given: &[Box<Obj>],
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.len() != given.len() {
            return Ok(None);
        }
        let mut merged = HashMap::new();
        for (left_arg, given_arg) in left.iter().zip(given.iter()) {
            let Some(sub_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
                left_arg.as_ref(),
                given_arg.as_ref(),
                anonymous_fn_body,
            )?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    fn match_forall_function_param_application_as_anonymous_fn(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::FnObj(fn_obj) = known_arg else {
            return Ok(None);
        };
        let FnObjHead::Forall(forall_param) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        if !Self::fn_obj_applies_to_exact_anonymous_fn_params(fn_obj, anonymous_fn_body) {
            return Ok(None);
        }

        let anonymous_fn = AnonymousFn::new(
            anonymous_fn_body.params_def_with_set.clone(),
            anonymous_fn_body.dom_facts.clone(),
            (*anonymous_fn_body.ret_set).clone(),
            given_arg.clone(),
        )?;
        let mut map = HashMap::new();
        map.insert(forall_param.name.clone(), anonymous_fn.into());
        Ok(Some(map))
    }

    fn fn_obj_applies_to_exact_anonymous_fn_params(
        fn_obj: &FnObj,
        anonymous_fn_body: &FnSetBody,
    ) -> bool {
        let expected_param_names = anonymous_fn_body.get_params();
        let expected_len = expected_param_names.len();
        let actual_args_count: usize = fn_obj.body.iter().map(|row| row.len()).sum();
        if actual_args_count != expected_len {
            return false;
        }

        let mut flat_index = 0;
        for row in fn_obj.body.iter() {
            for arg in row.iter() {
                let expected = obj_for_bound_param_in_scope(
                    expected_param_names[flat_index].clone(),
                    ParamObjType::FnSet,
                );
                if arg.to_string() != expected.to_string() {
                    return false;
                }
                flat_index += 1;
            }
        }
        true
    }

    fn match_fn_param_group_type_in_known_forall_with_given(
        &mut self,
        left: &ParamGroupWithSet,
        given: &ParamGroupWithSet,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.set_obj(),
            given.set_obj(),
        )
    }

    pub(crate) fn standard_set_is_subset_eq(subset: &StandardSet, superset: &StandardSet) -> bool {
        match (subset, superset) {
            (StandardSet::NPos, StandardSet::NPos)
            | (StandardSet::NPos, StandardSet::N)
            | (StandardSet::NPos, StandardSet::Z)
            | (StandardSet::NPos, StandardSet::Q)
            | (StandardSet::NPos, StandardSet::R)
            | (StandardSet::NPos, StandardSet::QPos)
            | (StandardSet::NPos, StandardSet::RPos)
            | (StandardSet::NPos, StandardSet::ZNz)
            | (StandardSet::NPos, StandardSet::QNz)
            | (StandardSet::NPos, StandardSet::RNz)
            | (StandardSet::N, StandardSet::N)
            | (StandardSet::N, StandardSet::Z)
            | (StandardSet::N, StandardSet::Q)
            | (StandardSet::N, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::ZNeg)
            | (StandardSet::ZNeg, StandardSet::Z)
            | (StandardSet::ZNeg, StandardSet::Q)
            | (StandardSet::ZNeg, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::QNeg)
            | (StandardSet::ZNeg, StandardSet::RNeg)
            | (StandardSet::ZNeg, StandardSet::ZNz)
            | (StandardSet::ZNeg, StandardSet::QNz)
            | (StandardSet::ZNeg, StandardSet::RNz)
            | (StandardSet::ZNz, StandardSet::ZNz)
            | (StandardSet::ZNz, StandardSet::Z)
            | (StandardSet::ZNz, StandardSet::Q)
            | (StandardSet::ZNz, StandardSet::R)
            | (StandardSet::ZNz, StandardSet::QNz)
            | (StandardSet::ZNz, StandardSet::RNz)
            | (StandardSet::Z, StandardSet::Z)
            | (StandardSet::Z, StandardSet::Q)
            | (StandardSet::Z, StandardSet::R)
            | (StandardSet::QPos, StandardSet::QPos)
            | (StandardSet::QPos, StandardSet::Q)
            | (StandardSet::QPos, StandardSet::R)
            | (StandardSet::QPos, StandardSet::RPos)
            | (StandardSet::QPos, StandardSet::QNz)
            | (StandardSet::QPos, StandardSet::RNz)
            | (StandardSet::QNeg, StandardSet::QNeg)
            | (StandardSet::QNeg, StandardSet::Q)
            | (StandardSet::QNeg, StandardSet::R)
            | (StandardSet::QNeg, StandardSet::RNeg)
            | (StandardSet::QNeg, StandardSet::QNz)
            | (StandardSet::QNeg, StandardSet::RNz)
            | (StandardSet::QNz, StandardSet::QNz)
            | (StandardSet::QNz, StandardSet::Q)
            | (StandardSet::QNz, StandardSet::R)
            | (StandardSet::QNz, StandardSet::RNz)
            | (StandardSet::Q, StandardSet::Q)
            | (StandardSet::Q, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RPos)
            | (StandardSet::RPos, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RNz)
            | (StandardSet::RNeg, StandardSet::RNeg)
            | (StandardSet::RNeg, StandardSet::R)
            | (StandardSet::RNeg, StandardSet::RNz)
            | (StandardSet::RNz, StandardSet::RNz)
            | (StandardSet::RNz, StandardSet::R)
            | (StandardSet::R, StandardSet::R) => true,
            _ => false,
        }
    }

    fn match_arg_when_left_is_n_pos_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_n_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::N) | Obj::StandardSet(StandardSet::NPos) => {
                self.match_arg_same_type(given_arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::N)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::N)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_obj(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::R)
            | Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::RNeg)
            | Obj::StandardSet(StandardSet::RNz)
            | Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::N)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart(
        &mut self,
        left_args: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Cart(ref given) => self.match_boxed_arg_vec_then_merge(left_args, &given.args),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_cart_dim(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::CartDim(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_proj(
        &mut self,
        left_set: &Obj,
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Proj(ref given) => self.match_arg_binary_then_merge(
                left_set,
                left_dim,
                given.set.as_ref(),
                given.dim.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_dim(
        &mut self,
        left_dim: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::TupleDim(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_dim,
                    given.arg.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_tuple(
        &mut self,
        left_elements: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Tuple(ref given) => {
                self.match_boxed_arg_vec_then_merge(left_elements, &given.args)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_finite_seq_list(
        &mut self,
        left_elements: &[Box<Obj>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSeqListObj(ref given) => {
                self.match_boxed_arg_vec_then_merge(left_elements, &given.objs)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_finite_set_size(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSetSize(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_fn_range(
        &mut self,
        left_function: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FnRange(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_function,
                    given.function.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_replacement(
        &mut self,
        left: &Replacement,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Replacement(given) => {
                if left.prop_name.to_string() != given.prop_name.to_string() {
                    return Ok(None);
                }
                self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left.source_set.as_ref(),
                    given.source_set.as_ref(),
                )
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_range(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Range(ref given) => self.match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_sum(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Sum(ref g) => self.match_arg_ternary_then_merge(
                left_start,
                left_end,
                left_func,
                g.start.as_ref(),
                g.end.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_finite_set_sum(
        &mut self,
        left_set: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SumOfFiniteSet(ref g) => self.match_arg_binary_then_merge(
                left_set,
                left_func,
                g.set.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_product(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::Product(ref g) => self.match_arg_ternary_then_merge(
                left_start,
                left_end,
                left_func,
                g.start.as_ref(),
                g.end.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_finite_set_product(
        &mut self,
        left_set: &Obj,
        left_func: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ProductOfFiniteSet(ref g) => self.match_arg_binary_then_merge(
                left_set,
                left_func,
                g.set.as_ref(),
                g.func.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_closed_range(
        &mut self,
        left_start: &Obj,
        left_end: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ClosedRange(ref given) => self.match_arg_binary_then_merge(
                left_start,
                left_end,
                given.start.as_ref(),
                given.end.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_interval(
        &mut self,
        left: &IntervalObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::IntervalObj(given) = given_arg else {
            return Ok(None);
        };
        if left.left_closed() != given.left_closed() || left.right_closed() != given.right_closed()
        {
            return Ok(None);
        }
        self.match_arg_binary_then_merge(left.start(), left.end(), given.start(), given.end())
    }

    fn match_arg_when_left_is_one_side_infinity_interval(
        &mut self,
        left: &OneSideInfinityIntervalObj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::OneSideInfinityIntervalObj(given) = given_arg else {
            return Ok(None);
        };
        if !left.same_kind_as(given) {
            return Ok(None);
        }
        self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(left.start(), given.start())
    }

    fn match_arg_when_left_is_finite_seq_set(
        &mut self,
        left_set: &Obj,
        left_n: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::FiniteSeqSet(ref given) => self.match_arg_binary_then_merge(
                left_set,
                left_n,
                given.set.as_ref(),
                given.n.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_seq_set(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::SeqSet(ref given) => self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                left_set,
                given.set.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_list(
        &mut self,
        left_rows: &[Vec<Box<Obj>>],
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixListObj(ref given) => {
                self.match_arg_matrix_rows_then_merge(left_rows, &given.rows)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_matrix_set(
        &mut self,
        left_set: &Obj,
        left_row_len: &Obj,
        left_col_len: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::MatrixSet(ref given) => self.match_arg_ternary_then_merge(
                left_set,
                left_row_len,
                left_col_len,
                given.set.as_ref(),
                given.row_len.as_ref(),
                given.col_len.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_power_set(
        &mut self,
        left_set: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::PowerSet(ref given) => self
                .match_arg_in_atomic_fact_in_known_forall_with_given_arg(
                    left_set,
                    given.set.as_ref(),
                ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_obj_at_index(
        &mut self,
        left_obj: &Obj,
        left_index: &Obj,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::ObjAtIndex(ref given) => self.match_arg_binary_then_merge(
                left_obj,
                left_index,
                given.obj.as_ref(),
                given.index.as_ref(),
            ),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_pos(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::QPos) | Obj::StandardSet(StandardSet::NPos) => {
                self.match_arg_same_type(given_arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_pos(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_neg(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::QNeg) | Obj::StandardSet(StandardSet::ZNeg) => {
                self.match_arg_same_type(given_arg)
            }
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_neg(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::ZNeg) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_neg(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::RNeg)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNeg) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_q_nz(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_z_nz(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_when_left_is_r_nz(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        match given_arg {
            Obj::StandardSet(StandardSet::RNz)
            | Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::RNeg)
            | Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::NPos) => self.match_arg_same_type(given_arg),
            _ => Ok(None),
        }
    }

    fn match_arg_same_type(
        &mut self,
        given_arg: &Obj,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let mut map = HashMap::new();
        map.insert(given_arg.to_string(), given_arg.clone());
        Ok(Some(map))
    }
}

fn atomic_fact_in_forall_lookup_arg_shape_keys(
    atomic_fact: &AtomicFact,
) -> Vec<AtomicFactInForallArgShapeKey> {
    let exact_key = atomic_fact_in_forall_arg_shape_key(atomic_fact);
    let forall_param_key_part = (ObjKind::ForallFreeParam, String::new());
    let mut keys = Vec::new();
    push_atomic_fact_in_forall_arg_shape_key_if_new(&mut keys, exact_key.clone());

    for index in 0..exact_key.len() {
        let known_keys_count = keys.len();
        for key_index in 0..known_keys_count {
            let mut key = keys[key_index].clone();
            key[index] = forall_param_key_part.clone();
            push_atomic_fact_in_forall_arg_shape_key_if_new(&mut keys, key);
        }
    }

    keys
}

fn push_atomic_fact_in_forall_arg_shape_key_if_new(
    keys: &mut Vec<AtomicFactInForallArgShapeKey>,
    key: AtomicFactInForallArgShapeKey,
) {
    if !keys.contains(&key) {
        keys.push(key);
    }
}

fn exist_body_facts_have_same_shape(
    left: &ExistBodyFact,
    right: &ExistBodyFact,
) -> Result<bool, RuntimeError> {
    match (left, right) {
        (ExistBodyFact::AtomicFact(left), ExistBodyFact::AtomicFact(right)) => {
            Runtime::_verify_atomic_fact_the_same_type_ref(left, right)
        }
        (ExistBodyFact::AndFact(left), ExistBodyFact::AndFact(right)) => {
            Runtime::_verify_and_fact_the_same_type_ref(left, right)
        }
        (ExistBodyFact::ChainFact(left), ExistBodyFact::ChainFact(right)) => {
            Runtime::_verify_chain_fact_the_same_type_ref(left, right)
        }
        (ExistBodyFact::OrFact(left), ExistBodyFact::OrFact(right)) => {
            Runtime::_verify_or_fact_the_same_type_ref(left, right)
        }
        (ExistBodyFact::InlineForall(left), ExistBodyFact::InlineForall(right)) => {
            Ok(left.to_string() == right.to_string())
        }
        _ => Ok(false),
    }
}
