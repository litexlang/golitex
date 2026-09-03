use crate::prelude::*;

impl Runtime {
    pub fn define_params_with_set(
        &mut self,
        param_def: &SetBoundParameterGroup,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.define_params_with_set_in_scope(param_def, BindingScope::LocalBinder)
    }

    pub fn define_params_with_set_in_scope(
        &mut self,
        param_def: &SetBoundParameterGroup,
        binding_scope: BindingScope,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if self.current_execution_is_trusted_file() {
            return self.define_set_bound_params_in_scope_with_trust(param_def, binding_scope);
        }

        let param_set = param_def.set_obj();
        self.verify_obj_well_defined_result(param_set, &VerifyState::initial())
            .map_err(|well_defined_error| {
                let param_names_text = vec_to_string_join_by_comma(&param_def.params);
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
        let mut infer_result = SuccessInferResult::new();
        let facts = param_def.facts();
        for (binding, fact) in param_def.params.iter().zip(facts.iter()) {
            let name = binding.name();
            self.store_set_bound_parameter_binding(binding, binding_scope, param_set)
                .map_err(|runtime_error| {
                    RuntimeError::from(DefineParamsRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "define params with set: failed to bind parameter `{}`",
                                name
                            ),
                            runtime_error,
                        ),
                    ))
                })?;
            let fact_infer_result = self
                .store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
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
            if let Obj::StructObj(struct_obj) = param_set {
                let parameter = param_binding_element_obj_for_store(binding, binding_scope);
                infer_result.new_infer_result_inside(self.release_one_struct_definition_layer(
                    &parameter,
                    struct_obj,
                    default_line_file(),
                    InferReason::ParameterDefinition.store_reason(),
                )?);
            }
        }
        Ok(infer_result)
    }

    fn define_set_bound_params_in_scope_with_trust(
        &mut self,
        param_def: &SetBoundParameterGroup,
        binding_scope: BindingScope,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut infer_result = SuccessInferResult::new();
        let facts = param_def.facts();
        for (binding, fact) in param_def.params.iter().zip(facts.iter()) {
            let name = binding.name();
            self.store_set_bound_parameter_binding(binding, binding_scope, param_def.set_obj())
                .map_err(|runtime_error| {
                    RuntimeError::from(DefineParamsRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "define params with set: failed to bind parameter `{}`",
                                name
                            ),
                            runtime_error,
                        ),
                    ))
                })?;
            let fact_infer_result = self
                .store_fact_with_trust_and_infer_with_reason(
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
            if let Obj::StructObj(struct_obj) = param_def.set_obj() {
                let parameter = param_binding_element_obj_for_store(binding, binding_scope);
                infer_result.new_infer_result_inside(self.release_one_struct_definition_layer(
                    &parameter,
                    struct_obj,
                    default_line_file(),
                    InferReason::ParameterDefinition.store_reason(),
                )?);
            }
        }
        Ok(infer_result)
    }
}
