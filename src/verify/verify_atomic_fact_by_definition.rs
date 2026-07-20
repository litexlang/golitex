use crate::prelude::*;

impl Runtime {
    // Built-in subset/superset definitions first, then user `prop` iff-clauses.
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
        let verify_forall_result = self.verify_fact_full(&membership_forall_fact, verify_state)?;
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
        let verify_forall_result = self.verify_fact_full(&membership_forall_fact, verify_state)?;
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

        let (args_param_types, clause_checks) = self.verify_normal_atomic_fact_definition_clauses(
            normal_atomic_fact,
            &definition,
            verify_state,
        )?;
        if args_param_types.is_unknown() {
            return Ok(None);
        }

        if definition.iff_facts.is_empty() {
            return Ok(None);
        }

        let mut infer_result = InferResult::new();
        for (_, clause_result) in clause_checks {
            if clause_result.is_unknown() {
                return Ok(None);
            }
            infer_result.new_infer_result_inside(clause_result.infer_result());
        }

        let verified_by_text = format!(
            "prop with meaning `{}` (param constraints and definition clauses)",
            predicate_name
        );
        let fact_by_definition: Fact = normal_atomic_fact.clone().into();
        infer_result.add_fact_by_definition(
            Some(fact_by_definition.clone()),
            Some(predicate_name),
            &fact_by_definition,
        );
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

    pub(crate) fn verify_normal_atomic_fact_definition_clauses(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
        definition: &DefPropStmt,
        verify_state: &VerifyState,
    ) -> Result<(StmtResult, Vec<(Fact, StmtResult)>), RuntimeError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let args_param_types = self
            .verify_args_satisfy_param_def_flat_types(
                &definition.params_def_with_type,
                &normal_atomic_fact.body,
                verify_state,
                ParamObjType::DefHeader,
            )
            .map_err(|_| {
                RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                    format!("failed to verify parameter types for {}", predicate_name),
                    normal_atomic_fact.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
        if args_param_types.is_unknown() {
            return Ok((args_param_types, vec![]));
        }

        let param_to_arg_map = definition
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(normal_atomic_fact.body.as_slice());
        let mut clause_checks = Vec::with_capacity(definition.iff_facts.len());
        for iff_fact in definition.iff_facts.iter() {
            let instantiated_iff_fact = self
                .inst_fact(iff_fact, &param_to_arg_map, ParamObjType::DefHeader, None)
                .map_err(|e| {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                        String::new(),
                        normal_atomic_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    )))
                })?;
            let clause_result = self.verify_fact_full(&instantiated_iff_fact, verify_state)?;
            let clause_is_unknown = clause_result.is_unknown();
            clause_checks.push((instantiated_iff_fact, clause_result));
            if clause_is_unknown {
                break;
            }
        }
        Ok((args_param_types, clause_checks))
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
            _ => {}
        }
        Ok(None)
    }
}
