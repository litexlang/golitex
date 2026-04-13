use crate::prelude::*;

impl Runtime {
    /// Infer `forall x in left: x in right` from `left subset right`.
    pub fn infer_subset_fact(
        &mut self,
        subset_fact: &SubsetFact,
    ) -> Result<InferResult, RuntimeError> {
        let generated_param_name = self.generate_random_unused_name();
        let parameter_definition = ParamGroupWithParamType::new(
            vec![generated_param_name.clone()],
            ParamType::Obj(subset_fact.left.clone()),
        );
        let in_fact_for_forall_then = InFact::new(
            generated_param_name.clone().into(),
            subset_fact.right.clone(),
            subset_fact.line_file.clone(),
        )
        .into();
        let inferred_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![parameter_definition]),
            vec![],
            vec![in_fact_for_forall_then],
            subset_fact.line_file.clone(),
        )
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&inferred_forall_fact);
        self.store_fact_without_well_defined_verified_and_infer(inferred_forall_fact)
            .map_err(|previous_error| {
                RuntimeError::new_infer_error_with_msg_position_previous_error(
                    format!(
                        "failed to store inferred forall fact while inferring `{}`",
                        subset_fact
                    ),
                    subset_fact.line_file.clone(),
                    Some(RuntimeError::ExecStmtError(previous_error)),
                )
            })?;
        Ok(infer_result)
    }

    /// Infer `forall x in right: x in left` from `left superset right`.
    pub fn infer_superset_fact(
        &mut self,
        superset_fact: &SupersetFact,
    ) -> Result<InferResult, RuntimeError> {
        let generated_param_name = self.generate_random_unused_name();
        let parameter_definition = ParamGroupWithParamType::new(
            vec![generated_param_name.clone()],
            ParamType::Obj(superset_fact.right.clone()),
        );
        let in_fact_for_forall_then = InFact::new(
            generated_param_name.clone().into(),
            superset_fact.left.clone(),
            superset_fact.line_file.clone(),
        )
        .into();
        let inferred_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![parameter_definition]),
            vec![],
            vec![in_fact_for_forall_then],
            superset_fact.line_file.clone(),
        )
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&inferred_forall_fact);
        self.store_fact_without_well_defined_verified_and_infer(inferred_forall_fact)
            .map_err(|previous_error| {
                RuntimeError::new_infer_error_with_msg_position_previous_error(
                    format!(
                        "failed to store inferred forall fact while inferring `{}`",
                        superset_fact
                    ),
                    superset_fact.line_file.clone(),
                    Some(RuntimeError::ExecStmtError(previous_error)),
                )
            })?;
        Ok(infer_result)
    }
}
