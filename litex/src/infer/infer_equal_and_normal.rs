use crate::error::InferError;
use crate::execute::Runtime;
use crate::fact::{EqualFact, NormalAtomicFact};
use crate::infer::InferResult;
use crate::stmt::parameter_def::ParamDefWithParamType;

impl<'a> Runtime<'a> {
    /// Infer from equality by syncing known calculated values.
    /// Example: from `a = 1 + 2`, remember `a -> 3`.
    pub(crate) fn infer_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<InferResult, InferError> {
        if let Some(right_calculated_value) =
            self.get_known_normalized_calculated_value_for_obj(&equal_fact.right)
        {
            self.runtime_context
                .top_level_env()
                .known_normalized_calculated_value_of_obj
                .insert(equal_fact.left.to_string(), right_calculated_value);
        }

        if let Some(left_calculated_value) =
            self.get_known_normalized_calculated_value_for_obj(&equal_fact.left)
        {
            self.runtime_context
                .top_level_env()
                .known_normalized_calculated_value_of_obj
                .insert(equal_fact.right.to_string(), left_calculated_value);
        }

        Ok(InferResult::new())
    }

    /// Infer predicate meaning by instantiating declared iff facts.
    /// Example: from `isEven(n)`, infer the instantiated definition facts.
    pub(crate) fn infer_normal_atomic_fact(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
    ) -> Result<InferResult, InferError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let predicate_definition = match self
            .runtime_context
            .get_predicate_with_meaning_definition_by_name(&predicate_name)
        {
            Some(predicate_definition) => predicate_definition.clone(),
            None => return Ok(InferResult::new()),
        };
        let mut infer_result = InferResult::new();

        let param_type_facts = ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(
            &predicate_definition.params_def_with_type,
            &normal_atomic_fact.body,
        )
        .map_err(|previous_error| {
            InferError::new(
                format!(
                    "failed to infer parameter type facts for `{}`",
                    normal_atomic_fact
                ),
                normal_atomic_fact.line_file,
                Some(previous_error),
            )
        })?;

        for param_type_fact in param_type_facts.iter() {
            let fact_to_store = param_type_fact
                .clone()
                .with_new_line_file(normal_atomic_fact.line_file);
            self.store_atomic_fact_without_well_defined_verified_and_infer(&fact_to_store)
                .map_err(|previous_error| {
                    InferError::new(
                        format!(
                            "failed to store parameter type fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
            infer_result.push_atomic_fact(&fact_to_store);
        }

        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &predicate_definition.params_def_with_type,
            &normal_atomic_fact.body,
        );

        for iff_fact in predicate_definition.iff_facts.iter() {
            let instantiated_iff_fact = iff_fact.instantiate(&param_to_arg_map);
            let fact_to_store = instantiated_iff_fact.with_new_line_file(normal_atomic_fact.line_file);
            self.store_fact_without_well_defined_verified_and_infer(&fact_to_store)
                .map_err(|previous_error| {
                    InferError::new(
                        format!(
                            "failed to store instantiated iff fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
            infer_result.new_fact(&fact_to_store);
        }

        Ok(infer_result)
    }
}
