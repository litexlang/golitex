use crate::prelude::*;

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
        if self.only_exec_affect_environment {
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
    /// When defining `x S`, if the environment already has `S $subset T`, record
    /// `x $in T` in the same local environment. This supports function bodies such
    /// as `fn(x E) R {f(x)}` when `E $subset E2` and `f fn(x E2) R`, without making
    /// every ordinary membership fact recursively infer through all known subsets.
    fn store_param_memberships_in_known_supersets(
        &mut self,
        name: &str,
        binding_scope: ParamObjType,
        param_set: &Obj,
        source_fact: Fact,
    ) -> Result<InferResult, RuntimeError> {
        let lookup_key = (SUBSET.to_string(), true);
        let source_set_key = param_set.to_string();
        let mut target_sets: Vec<Obj> = Vec::new();
        for env in self.iter_environments_from_top() {
            let Some(known_subset_facts) = env.known_atomic_facts_with_2_args.get(&lookup_key)
            else {
                continue;
            };
            for ((left_key, _), known_fact) in known_subset_facts.iter() {
                if left_key != &source_set_key {
                    continue;
                }
                let AtomicFact::SubsetFact(subset_fact) = known_fact else {
                    continue;
                };
                target_sets.push(subset_fact.right.clone());
            }
        }

        let param_obj = obj_for_bound_param_in_scope(name.to_string(), binding_scope);
        let mut infer_result = InferResult::new();
        for target_set in target_sets {
            if target_set.to_string() == source_set_key {
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
