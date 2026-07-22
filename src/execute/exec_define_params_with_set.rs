use crate::prelude::*;
use std::collections::{HashSet, VecDeque};

impl Runtime {
    pub fn define_params_with_set(
        &mut self,
        param_def: &ParamGroupWithSet,
    ) -> Result<InferResult, RuntimeError> {
        self.define_params_with_set_in_scope(param_def, ParamObjType::FnSet)
    }

    pub fn define_params_with_set_in_scope(
        &mut self,
        param_def: &ParamGroupWithSet,
        binding_scope: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        if self.current_execution_is_trusted_file() {
            return self.define_params_with_set_in_scope_trusted(param_def, binding_scope);
        }

        let param_set = param_def.set_obj();
        self.verify_obj_well_defined_and_store_cache(param_set, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                let param_names_text = param_def.params.join(", ");
                let error_line_file = well_defined_error.line_file().clone();
                RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new(
                    None,
                    format!(
                        "define params with set: failed to verify set well-defined for params [{}] with set {}",
                        param_names_text, param_set
                    ),
                    error_line_file,
                    Some(well_defined_error),
                    vec![],
                )))
            })?;
        let mut infer_result = InferResult::new();
        let facts = param_def.facts_for_binding_scope(binding_scope);
        for (name, fact) in param_def.params.iter().zip(facts.iter()) {
            self.store_free_param_or_identifier_name(name, binding_scope)
                .map_err(|runtime_error| {
                    RuntimeError::from(DefineParamsRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "define params with set: failed to declare parameter `{}`",
                                name
                            ),
                            runtime_error,
                        ),
                    ))
                })?;
            let fact_infer_result = self
                .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                    fact.clone(),
                    InferReason::ParameterDefinition,
                )
                .map_err(|store_fact_error| {
                    RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                            "define params with set: failed to store in-set fact for parameter `{}`",
                            name
                        ), store_fact_error)))
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
            infer_result.new_infer_result_inside(self.store_param_memberships_in_known_supersets(
                name,
                binding_scope,
                param_set,
                fact.clone(),
            )?);
        }
        Ok(infer_result)
    }

    fn define_params_with_set_in_scope_trusted(
        &mut self,
        param_def: &ParamGroupWithSet,
        binding_scope: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let param_set = param_def.set_obj();
        let mut infer_result = InferResult::new();
        let facts = param_def.facts_for_binding_scope(binding_scope);
        for (name, fact) in param_def.params.iter().zip(facts.iter()) {
            self.store_free_param_or_identifier_name(name, binding_scope)
                .map_err(|runtime_error| {
                    RuntimeError::from(DefineParamsRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "define params with set: failed to declare parameter `{}`",
                                name
                            ),
                            runtime_error,
                        ),
                    ))
                })?;
            let fact_infer_result = self
                .store_trusted_fact_and_infer_with_reason(
                    fact.clone(),
                    InferReason::ParameterDefinition,
                )
                .map_err(|store_fact_error| {
                    RuntimeError::from(DefineParamsRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "define params with set: failed to store in-set fact for parameter `{}`",
                                name
                            ),
                            store_fact_error,
                        ),
                    ))
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
            infer_result.new_infer_result_inside(self.store_param_memberships_in_known_supersets(
                name,
                binding_scope,
                param_set,
                fact.clone(),
            )?);
        }
        Ok(infer_result)
    }

    /// Parameter membership bridge through already-known subset facts.
    /// When defining `x S`, follow the known subset graph from `S` and record
    /// `x $in T` for every reachable superset `T` in the same local environment.
    /// Example: `S $subset U` and `U $subset T` let a parameter `x S` infer both
    /// `x $in U` and `x $in T`, without recursively expanding arbitrary membership
    /// facts outside parameter definition.
    pub(crate) fn store_param_memberships_in_known_supersets(
        &mut self,
        name: &str,
        binding_scope: ParamObjType,
        param_set: &Obj,
        source_fact: Fact,
    ) -> Result<InferResult, RuntimeError> {
        let lookup_key = (SUBSET.to_string(), true);
        let source_set_key = param_set.to_string();
        let mut source_set_keys = vec![source_set_key.clone()];
        let mut search_environments = self.iter_environments_from_top().collect::<Vec<_>>();
        if let Obj::Atom(AtomObj::IdentifierWithMod(identifier)) = param_set {
            if self.is_current_parse_module(&identifier.mod_name) {
                source_set_keys.push(identifier.name.clone());
            } else {
                search_environments.extend(self.imported_module_environments(&identifier.mod_name));
            }
        }
        let mut subset_edges = Vec::new();
        for env in search_environments {
            let Some(known_subset_facts) = env.known_atomic_facts_with_2_args.get(&lookup_key)
            else {
                continue;
            };
            for known_fact in known_subset_facts.values() {
                let AtomicFact::SubsetFact(subset_fact) = known_fact else {
                    continue;
                };
                let mut left_keys = vec![subset_fact.left.to_string()];
                if let Obj::Atom(AtomObj::IdentifierWithMod(identifier)) = &subset_fact.left {
                    if self.is_current_parse_module(&identifier.mod_name) {
                        left_keys.push(identifier.name.clone());
                    }
                }
                let mut right_keys = vec![subset_fact.right.to_string()];
                if let Obj::Atom(AtomObj::IdentifierWithMod(identifier)) = &subset_fact.right {
                    if self.is_current_parse_module(&identifier.mod_name) {
                        right_keys.push(identifier.name.clone());
                    }
                }
                subset_edges.push((left_keys, subset_fact.right.clone(), right_keys));
            }
        }

        let mut pending_set_keys = VecDeque::new();
        let mut reachable_set_keys = HashSet::new();
        for source_set_key in source_set_keys.iter() {
            if reachable_set_keys.insert(source_set_key.clone()) {
                pending_set_keys.push_back(source_set_key.clone());
            }
        }
        let mut target_sets = Vec::new();
        let mut target_set_keys = HashSet::new();
        while let Some(current_set_key) = pending_set_keys.pop_front() {
            for (left_keys, right, right_keys) in subset_edges.iter() {
                if !left_keys
                    .iter()
                    .any(|left_key| left_key == &current_set_key)
                {
                    continue;
                }
                if target_set_keys.insert(right.to_string()) {
                    target_sets.push((right.clone(), right_keys.clone()));
                }
                for right_key in right_keys {
                    if reachable_set_keys.insert(right_key.clone()) {
                        pending_set_keys.push_back(right_key.clone());
                    }
                }
            }
        }

        let param_obj = param_binding_element_obj_for_store(name.to_string(), binding_scope);
        let mut infer_result = InferResult::new();
        for (target_set, target_keys) in target_sets {
            if target_keys
                .iter()
                .any(|target_key| source_set_keys.contains(target_key))
            {
                continue;
            }
            let inferred_fact: AtomicFact =
                InFact::new(param_obj.clone(), target_set, default_line_file()).into();
            let inferred_fact_string = inferred_fact.to_string();
            if self.cache_known_facts_contains(&inferred_fact_string).0 {
                continue;
            }
            let inferred_fact_line_file = inferred_fact.line_file();
            let inferred_fact_as_fact: Fact = inferred_fact.clone().into();
            self.top_level_env().store_atomic_fact(inferred_fact)?;
            self.top_level_env()
                .store_fact_to_cache_known_fact(inferred_fact_string, inferred_fact_line_file)?;
            infer_result.add_builtin_inference(
                "parameter membership through known subset",
                Some(source_fact.clone()),
                &inferred_fact_as_fact,
            );
        }
        Ok(infer_result)
    }
}
