use crate::prelude::*;

impl Runtime {
    // Subset: `A $subset B` => `forall` fresh `x`: `x $in A` => `x $in B`.
    // Example: knowing `S $subset T`, any member of `S` is a member of `T`.
    pub fn infer_subset_fact(
        &mut self,
        subset_fact: &SubsetFact,
    ) -> Result<InferResult, RuntimeError> {
        let left_set = subset_fact.left.clone();
        let left_is_set_builder = matches!(&left_set, Obj::SetBuilder(_))
            || matches!(
                self.unfold_known_fn_application_once(&left_set, &VerifyState::new(0, false))?,
                Some(Obj::SetBuilder(_))
            )
            || self
                .get_obj_equal_to_set_builder(&left_set.to_string())
                .is_some();
        let mut left_has_set_builder_representative = false;
        for representative in self
            .get_all_obj_representatives_equal_to_given(&left_set)
            .into_iter()
        {
            if matches!(&representative, Obj::SetBuilder(_))
                || self
                    .get_obj_equal_to_set_builder(&representative.to_string())
                    .is_some()
                || matches!(
                    self.unfold_known_fn_application_once(
                        &representative,
                        &VerifyState::new(0, false),
                    )?,
                    Some(Obj::SetBuilder(_))
                )
            {
                left_has_set_builder_representative = true;
                break;
            }
        }
        if left_is_set_builder || left_has_set_builder_representative {
            // A set-builder membership already infers its parameter-domain fact
            // and filter facts.  Do not build `forall x builder: ...`: defining
            // that parameter rechecks the builder filter before its domain fact
            // is in scope.  The same applies to a symbolic set already equal to
            // a builder. Example: `C = {y E: P(y)}`, `C $subset R`.
            return Ok(InferResult::new());
        }
        let generated_param_name = self.generate_random_unused_name();
        let parameter_definition = ParamGroupWithParamType::new(
            vec![generated_param_name.clone()],
            ParamType::Obj(subset_fact.left.clone()),
        );
        let in_fact_for_forall_then = InFact::new(
            obj_for_bound_param_in_scope(generated_param_name.clone(), ParamObjType::Forall),
            subset_fact.right.clone(),
            subset_fact.line_file.clone(),
        )
        .into();
        let inferred_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![parameter_definition]),
            vec![],
            vec![in_fact_for_forall_then],
            subset_fact.line_file.clone(),
        )?
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&inferred_forall_fact);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
            inferred_forall_fact,
        )
        .map_err(|previous_error| {
            RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "failed to store inferred forall fact while inferring `{}`",
                    subset_fact
                ),
                subset_fact.line_file.clone(),
                Some(previous_error),
                vec![],
            )))
        })?;
        Ok(infer_result)
    }

    // Superset: `A $superset B` => `forall` fresh `x`: `x $in B` => `x $in A`.
    // Example: knowing `T $superset S`, every `x $in S` satisfies `x $in T`.
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
            obj_for_bound_param_in_scope(generated_param_name.clone(), ParamObjType::Forall),
            superset_fact.left.clone(),
            superset_fact.line_file.clone(),
        )
        .into();
        let inferred_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![parameter_definition]),
            vec![],
            vec![in_fact_for_forall_then],
            superset_fact.line_file.clone(),
        )?
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&inferred_forall_fact);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
            inferred_forall_fact,
        )
        .map_err(|previous_error| {
            RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "failed to store inferred forall fact while inferring `{}`",
                    superset_fact
                ),
                superset_fact.line_file.clone(),
                Some(previous_error),
                vec![],
            )))
        })?;
        Ok(infer_result)
    }
}
