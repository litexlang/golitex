use crate::prelude::*;

impl Runtime {
    // Built-in subset/superset/restrict_fn_in definitions first, then user `prop` iff-clauses.
    pub(crate) fn verify_atomic_fact_using_builtin_or_prop_definition(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) =
            self.verify_builtin_fact_with_their_definition(atomic_fact, verify_state)?
        {
            return Ok(Some(result));
        }
        if let AtomicFact::NormalAtomicFact(n) = atomic_fact {
            return self.verify_normal_atomic_fact_using_its_definition(n, verify_state);
        }
        Ok(None)
    }

    fn verify_subset_fact_by_membership_forall_definition(
        &mut self,
        subset_fact: &SubsetFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let bound_param_name = self.generate_random_unused_name();
        let membership_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![bound_param_name.clone()],
                ParamType::Obj(subset_fact.left.clone()),
            )]),
            vec![],
            vec![InFact::new(
                obj_for_bound_param_in_scope(bound_param_name.clone(), ParamObjType::Forall),
                subset_fact.right.clone(),
                subset_fact.line_file.clone(),
            )
            .into()],
            subset_fact.line_file.clone(),
        )?
        .into();
        let verify_forall_result = self.verify_fact(&membership_forall_fact, verify_state)?;
        if !verify_forall_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                subset_fact.clone().into(),
                "subset by definition (forall x in left: x in right)".to_string(),
                Vec::new(),
            ))
            .into(),
        ))
    }

    fn verify_superset_fact_by_membership_forall_definition(
        &mut self,
        superset_fact: &SupersetFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let bound_param_name = self.generate_random_unused_name();
        let membership_forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![bound_param_name.clone()],
                ParamType::Obj(superset_fact.right.clone()),
            )]),
            vec![],
            vec![InFact::new(
                obj_for_bound_param_in_scope(bound_param_name.clone(), ParamObjType::Forall),
                superset_fact.left.clone(),
                superset_fact.line_file.clone(),
            )
            .into()],
            superset_fact.line_file.clone(),
        )?
        .into();
        let verify_forall_result = self.verify_fact(&membership_forall_fact, verify_state)?;
        if !verify_forall_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                superset_fact.clone().into(),
                "superset by definition (forall x in right: x in left)".to_string(),
                Vec::new(),
            ))
            .into(),
        ))
    }

    fn verify_normal_atomic_fact_using_its_definition(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(_) =
            self.get_abstract_prop_definition_by_name(&normal_atomic_fact.predicate.to_string())
        {
            return Ok(None);
        }

        let predicate_name = normal_atomic_fact.predicate.to_string();

        let raw_prop_definition_exists =
            self.get_prop_definition_by_name(&predicate_name).is_some();
        let definition = match self.get_active_prop_definition_by_name(&predicate_name) {
            Some(definition_reference) => definition_reference,
            None if raw_prop_definition_exists => return Ok(None),
            None => {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                        format!("prop definition not found for {}", predicate_name),
                        normal_atomic_fact.line_file.clone(),
                        None,
                        vec![],
                    ))
                    .into()
                })
            }
        };

        let verify_state_for_definition_clauses = verify_state;

        let args_param_types = match self.verify_args_satisfy_param_def_flat_types(
            &definition.params_def_with_type,
            &normal_atomic_fact.body,
            verify_state_for_definition_clauses,
            ParamObjType::DefHeader,
        ) {
            Ok(x) => x,
            Err(_) => {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                        format!("failed to verify parameter types for {}", predicate_name),
                        normal_atomic_fact.line_file.clone(),
                        None,
                        vec![],
                    ))
                    .into()
                })
            }
        };
        if args_param_types.is_unknown() {
            return Ok(None);
        }

        if definition.iff_facts.is_empty() {
            return Ok(None);
        }

        let param_to_arg_map = definition
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(normal_atomic_fact.body.as_slice());

        let mut infer_result = InferResult::new();

        for iff_fact in definition.iff_facts.iter() {
            let instantiated_iff_fact = self
                .inst_fact(iff_fact, &param_to_arg_map, ParamObjType::DefHeader, None)
                .map_err(|e| {
                    {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                            String::new(),
                            normal_atomic_fact.line_file.clone(),
                            Some(e),
                            vec![],
                        )))
                    }
                })?;
            let iff_clause_verify_result =
                self.verify_fact(&instantiated_iff_fact, &verify_state_for_definition_clauses)?;
            if iff_clause_verify_result.is_unknown() {
                return Ok(None);
            }
            match &iff_clause_verify_result {
                StmtResult::FactualStmtSuccess(factual_success) => {
                    infer_result.new_infer_result_inside(factual_success.infers.clone());
                }
                StmtResult::NonFactualStmtSuccess(non_factual_success) => {
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                StmtResult::StmtUnknown(_) => return Ok(None),
            }
        }

        let verified_by_text = format!(
            "prop with meaning `{}` (param constraints and definition clauses)",
            predicate_name
        );
        infer_result.new_fact(&normal_atomic_fact.clone().into());
        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_known_fact_and_infer(
                normal_atomic_fact.clone().into(),
                infer_result,
                VerifiedByResult::cited_stmt(
                    normal_atomic_fact.clone().into(),
                    definition.clone().into(),
                    Some(verified_by_text),
                ),
                Vec::new(),
            ))
            .into(),
        ))
    }

    fn verify_builtin_fact_with_their_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        match fact {
            AtomicFact::SubsetFact(subset_fact) => {
                if let Some(verified_by_subset_definition) = self
                    .verify_subset_fact_by_membership_forall_definition(subset_fact, verify_state)?
                {
                    return Ok(Some(verified_by_subset_definition));
                }
                return Ok(None);
            }
            AtomicFact::SupersetFact(superset_fact) => {
                if let Some(verified_by_superset_definition) = self
                    .verify_superset_fact_by_membership_forall_definition(
                        superset_fact,
                        verify_state,
                    )?
                {
                    return Ok(Some(verified_by_superset_definition));
                }
                return Ok(None);
            }
            AtomicFact::RestrictFact(restrict_fact) => {
                if let Some(verified_by_restrict_definition) =
                    self.verify_restrict_fact_using_its_definition(restrict_fact, verify_state)?
                {
                    return Ok(Some(verified_by_restrict_definition));
                }
                return Ok(None);
            }
            _ => {}
        }
        Ok(None)
    }
}
