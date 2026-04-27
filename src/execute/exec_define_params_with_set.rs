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
        self.verify_obj_well_defined_and_store_cache(&param_def.set, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                let param_names_text = param_def.params.join(", ");
                let error_line_file = well_defined_error.line_file().clone();
                RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new(
                    None,
                    format!(
                        "define params with set: failed to verify set well-defined for params [{}] with set {}",
                        param_names_text, param_def.set
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
                    RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                            "define params with set: failed to declare parameter `{}`",
                            name
                        ), runtime_error)))
                })?;
            let fact_infer_result = self
                .verify_well_defined_and_store_and_infer_with_default_verify_state(fact.clone())
                .map_err(|store_fact_error| {
                    RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                            "define params with set: failed to store in-set fact for parameter `{}`",
                            name
                        ), store_fact_error)))
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }
}
