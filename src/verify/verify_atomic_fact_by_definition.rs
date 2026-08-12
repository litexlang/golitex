use crate::prelude::*;

impl Runtime {
    fn verify_definition_clause_from_known_cache(
        &mut self,
        clause: &Fact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) = self.verify_fact_from_cache_using_display_string(clause) {
            return Ok(Some(result));
        }
        match clause {
            Fact::ForallFact(forall_fact) => {
                let key = self.alpha_normalized_forall_cache_key(forall_fact)?;
                let Some(cached_fact) = self.cached_known_fact(&key) else {
                    return Ok(None);
                };
                Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_known_fact(
                        clause.clone(),
                        VerifiedByResult::cached_fact(
                            clause.clone(),
                            cached_fact.line_file.clone(),
                            cached_fact.fact_id,
                        ),
                        Vec::new(),
                    )
                    .into(),
                ))
            }
            Fact::ExistFact(exist_fact) => {
                let result =
                    self.verify_exist_fact_with_known_exist_fact(exist_fact, exist_fact)?;
                Ok(result.is_true().then_some(result))
            }
            _ => Ok(None),
        }
    }

    pub(crate) fn verify_prime_fact_by_definition(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let AtomicFact::NormalAtomicFact(normal_fact) = atomic_fact else {
            return Ok(None);
        };
        let Some(definition_facts) = self.builtin_prime_definition_facts(normal_fact)? else {
            return Ok(None);
        };
        let mut subgoals = Vec::new();
        for definition_fact in definition_facts {
            let result = self.verify_fact_full(&definition_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
            subgoals.push(result);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "prime by trial-division definition".to_string(),
                subgoals,
            )
            .into(),
        ))
    }

    // Built-in subset/superset definitions first, then user `prop` iff-clauses.
    pub(crate) fn verify_atomic_fact_using_builtin_or_prop_definition(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) = self.verify_prime_fact_by_definition(atomic_fact, verify_state)? {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.verify_builtin_fact_with_their_definition(atomic_fact, verify_state)?
        {
            return Ok(Some(result));
        }
        if crate::verify::verify_proper_set_relations_builtin::is_builtin_proper_set_relation_fact(
            atomic_fact,
        ) {
            return Ok(None);
        }
        if let AtomicFact::NormalAtomicFact(n) = atomic_fact {
            return self.verify_normal_atomic_fact_using_its_definition(n, verify_state);
        }
        Ok(None)
    }

    fn verify_subset_fact_by_membership_forall_definition(
        &mut self,
        subset_fact: &SubsetFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let bound_param_name = self.generate_random_unused_name();
        let bound_param = self.fresh_param_group_with_type(
            vec![bound_param_name],
            ParamType::Obj(subset_fact.left.clone()),
        )?;
        let membership_forall_fact = ForallFact::new_canonical_forall(
            ParamDefWithType::new(vec![bound_param.clone()]),
            vec![],
            vec![InFact::new(
                obj_for_bound_param_in_scope(&bound_param.params[0], ParamObjType::Forall),
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
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let bound_param_name = self.generate_random_unused_name();
        let bound_param = self.fresh_param_group_with_type(
            vec![bound_param_name],
            ParamType::Obj(superset_fact.right.clone()),
        )?;
        let membership_forall_fact = ForallFact::new_canonical_forall(
            ParamDefWithType::new(vec![bound_param.clone()]),
            vec![],
            vec![InFact::new(
                obj_for_bound_param_in_scope(&bound_param.params[0], ParamObjType::Forall),
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
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) =
            self.verify_builtin_function_property_by_definition(normal_atomic_fact, verify_state)?
        {
            return Ok(Some(result));
        }

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
        infer_result.add_fact_by_definition(&fact_by_definition);
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
        verify_state: &UseContextVerifyState,
    ) -> Result<(StmtResult, Vec<(Fact, StmtResult)>), RuntimeError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let full_param_type_result = self.verify_args_satisfy_param_def_flat_types(
            &definition.params_def_with_type,
            &normal_atomic_fact.body,
            verify_state,
            ParamObjType::DefHeader,
        );
        let map_param_type_error = |_| {
            RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                format!("failed to verify parameter types for {}", predicate_name),
                normal_atomic_fact.line_file.clone(),
                None,
                vec![],
            )))
        };

        // Preserve the original order and all inference side effects whenever ordinary parameter
        // verification succeeds. The bounded cache route is only a liveness fallback.
        if matches!(&full_param_type_result, Ok(result) if !result.is_unknown()) {
            let args_param_types = full_param_type_result.map_err(map_param_type_error)?;
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
            return Ok((args_param_types, clause_checks));
        }

        // Only one exact quantified definition clause may use the fallback. Atomic and
        // multi-clause definitions keep the old unknown/error result without any cache probe.
        if definition.iff_facts.len() != 1 {
            let result = full_param_type_result.map_err(map_param_type_error)?;
            return Ok((result, vec![]));
        }
        let param_to_arg_map = definition
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(normal_atomic_fact.body.as_slice());
        let instantiated_clause = self
            .inst_fact(
                &definition.iff_facts[0],
                &param_to_arg_map,
                ParamObjType::DefHeader,
                None,
            )
            .map_err(|e| {
                RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(normal_atomic_fact.clone()).into_stmt()),
                    String::new(),
                    normal_atomic_fact.line_file.clone(),
                    Some(e),
                    vec![],
                )))
            })?;
        if !matches!(
            instantiated_clause,
            Fact::ForallFact(_) | Fact::ExistFact(_)
        ) {
            let result = full_param_type_result.map_err(map_param_type_error)?;
            return Ok((result, vec![]));
        }
        let Some(cached_clause_result) =
            self.verify_definition_clause_from_known_cache(&instantiated_clause)?
        else {
            let result = full_param_type_result.map_err(map_param_type_error)?;
            return Ok((result, vec![]));
        };
        let args_param_types = self
            .verify_args_satisfy_param_def_known_or_builtin_only(
                &definition.params_def_with_type,
                &normal_atomic_fact.body,
                verify_state,
                ParamObjType::DefHeader,
            )
            .map_err(map_param_type_error)?;
        if args_param_types.is_unknown() {
            return Ok((args_param_types, vec![]));
        }
        Ok((
            args_param_types,
            vec![(instantiated_clause, cached_clause_result)],
        ))
    }

    fn verify_builtin_fact_with_their_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
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
