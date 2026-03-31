use crate::prelude::*;

impl Runtime {
    /// Infer `forall x in left: x in right` from `left subset right`.
    pub(crate) fn infer_subset_fact(
        &mut self,
        subset_fact: &SubsetFact,
    ) -> Result<InferResult, InferError> {
        let generated_param_name = self.generate_a_random_unused_name();
        let parameter_definition = ParamDefWithParamType(
            vec![generated_param_name.clone()],
            ParamType::Obj(subset_fact.left.clone()),
        );
        let in_fact_for_forall_then =
            ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(generated_param_name.clone())),
                subset_fact.right.clone(),
                subset_fact.line_file,
            )));
        let inferred_forall_fact = Fact::ForallFact(ForallFact::new(
            vec![parameter_definition],
            vec![],
            vec![in_fact_for_forall_then],
            subset_fact.line_file,
        ));

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&inferred_forall_fact);
        self.store_fact_without_well_defined_verified_and_infer(inferred_forall_fact)
            .map_err(|previous_error| {
                InferError::new(
                    format!(
                        "failed to store inferred forall fact while inferring `{}`",
                        subset_fact
                    ),
                    subset_fact.line_file,
                    Some(previous_error.into()),
                )
            })?;
        Ok(infer_result)
    }

    /// Infer `forall x in right: x in left` from `left superset right`.
    pub(crate) fn infer_superset_fact(
        &mut self,
        superset_fact: &SupersetFact,
    ) -> Result<InferResult, InferError> {
        let generated_param_name = self.generate_a_random_unused_name();
        let parameter_definition = ParamDefWithParamType(
            vec![generated_param_name.clone()],
            ParamType::Obj(superset_fact.right.clone()),
        );
        let in_fact_for_forall_then =
            ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(generated_param_name.clone())),
                superset_fact.left.clone(),
                superset_fact.line_file,
            )));
        let inferred_forall_fact = Fact::ForallFact(ForallFact::new(
            vec![parameter_definition],
            vec![],
            vec![in_fact_for_forall_then],
            superset_fact.line_file,
        ));

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&inferred_forall_fact);
        self.store_fact_without_well_defined_verified_and_infer(inferred_forall_fact)
            .map_err(|previous_error| {
                InferError::new(
                    format!(
                        "failed to store inferred forall fact while inferring `{}`",
                        superset_fact
                    ),
                    superset_fact.line_file,
                    Some(previous_error.into()),
                )
            })?;
        Ok(infer_result)
    }
}
