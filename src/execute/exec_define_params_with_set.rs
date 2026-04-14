use crate::prelude::*;

impl Runtime {
    pub fn define_params_with_set(
        &mut self,
        param_def: &ParamGroupWithSet,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&param_def.set, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                let param_names_text = param_def.params.join(", ");
                let error_line_file = well_defined_error.line_file().clone();
                RuntimeError::new_define_params_error_with_msg_previous_error_position(
                    format!(
                        "define params with set: failed to verify set well-defined for params [{}] with set {}",
                        param_names_text, param_def.set
                    ),
                    Some(well_defined_error),
                    error_line_file,
                )
            })?;
        let mut infer_result = InferResult::new();
        let facts = param_def.facts();
        for (name, fact) in param_def.params.iter().zip(facts.iter()) {
            self.store_identifier_obj(name).map_err(|runtime_error| {
                RuntimeError::new_define_params_error_with_msg_previous_error_position(
                    format!(
                        "define params with set: failed to declare parameter `{}`",
                        name
                    ),
                    Some(runtime_error),
                    default_line_file(),
                )
            })?;
            let fact_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(fact.clone())
                .map_err(|store_fact_error| {
                    RuntimeError::new_define_params_error_with_msg_previous_error_position(
                        format!(
                            "define params with set: failed to store in-set fact for parameter `{}`",
                            name
                        ),
                        Some(store_fact_error),
                        default_line_file(),
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }
}
