use crate::prelude::*;

impl Runtime {
    pub fn exec_def_struct_stmt(
        &mut self,
        def_struct_stmt: &DefStructStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let is_trusted = self.current_execution_is_trusted_file();
        let run_in_local_env = self
            .run_in_local_env(|rt| {
                if is_trusted {
                    rt.def_struct_stmt_check_well_defined_without_result(def_struct_stmt)?;
                    Ok(None)
                } else {
                    rt.def_struct_stmt_check_well_defined_result(def_struct_stmt)
                        .map(Some)
                }
            })
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_struct_stmt.clone().into(), e))?;
        self.store_def_struct(def_struct_stmt)?;
        Ok(
            SuccessDefinitionStmtResult::DefStructStmt(Box::new(SuccessDefStructStmtResult {
                statement: def_struct_stmt.clone(),
                common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                run_in_local_env,
            }))
            .into(),
        )
    }

    /// Mathematical contract: a struct definition has meaningful header
    /// parameters and domain facts, meaningful field carriers, and meaningful
    /// equivalent facts under locally bound fields of those carriers.
    fn def_struct_stmt_check_well_defined_without_result(
        &mut self,
        def_struct_stmt: &DefStructStmt,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::initial();

        if let Some((param_def_with_type, dom_facts)) = &def_struct_stmt.param_def_with_dom {
            self.define_params_with_type(param_def_with_type, false, BindingScope::LocalBinder)?;
            for dom_fact in dom_facts.iter() {
                self.verify_quantifier_free_fact_well_defined(dom_fact, &verify_state)?;
            }
        }

        for field in def_struct_stmt.fields.iter() {
            self.verify_obj_well_defined_and_store_cache(&field.field_type, &verify_state)?;
        }

        self.run_in_local_env(|rt| {
            for field in def_struct_stmt.fields.iter() {
                let param_def = SetBoundParameterGroup::new(
                    vec![field.binding.clone()],
                    field.field_type.clone(),
                );
                rt.define_params_with_set_in_scope(&param_def, BindingScope::StructureField)?;
            }

            for fact in def_struct_stmt.equivalent_facts.iter() {
                rt.verify_well_defined_and_store_without_infer(
                    fact.clone(),
                    InferReason::ByDefinition,
                )?;
            }
            Ok::<(), RuntimeError>(())
        })?;

        Ok(())
    }

    /// Result-producing form of the definition check. Each field is the
    /// direct output of the matching semantic operation; no verification or
    /// store is replayed merely to assemble the statement Result.
    fn def_struct_stmt_check_well_defined_result(
        &mut self,
        def_struct_stmt: &DefStructStmt,
    ) -> Result<SuccessVerifyDefStructLocalEnvResult, RuntimeError> {
        let verify_state = VerifyState::initial();

        let mut structure_parameter_definition = None;
        let mut structure_domains = Vec::new();
        if let Some((param_def_with_type, dom_facts)) = &def_struct_stmt.param_def_with_dom {
            let mut infers = self.define_params_with_type(
                param_def_with_type,
                false,
                BindingScope::LocalBinder,
            )?;
            self.attach_known_fact_ids_to_infer_result(&mut infers)?;
            structure_parameter_definition = Some(infers);

            structure_domains.reserve(dom_facts.len());
            for (domain_index, dom_fact) in dom_facts.iter().enumerate() {
                let proposition: Fact = dom_fact.clone().into();
                let well_definedness =
                    self.verify_fact_well_defined_result(&proposition, &verify_state)?;
                structure_domains.push(SuccessVerifyDefStructDomainResult {
                    domain_index,
                    proposition,
                    well_definedness,
                });
            }
        }

        let mut field_types = Vec::with_capacity(def_struct_stmt.fields.len());
        for (field_index, field) in def_struct_stmt.fields.iter().enumerate() {
            let well_definedness =
                self.verify_obj_well_defined_result(&field.field_type, &verify_state)?;
            field_types.push(SuccessVerifyDefStructFieldTypeResult {
                field_index,
                binding: field.binding.clone(),
                field_type: field.field_type.clone(),
                well_definedness,
            });
        }

        let field_scope_run_in_local_env = self.run_in_local_env(|rt| {
            let mut field_definitions = Vec::with_capacity(def_struct_stmt.fields.len());
            for (field_index, field) in def_struct_stmt.fields.iter().enumerate() {
                let param_def = SetBoundParameterGroup::new(
                    vec![field.binding.clone()],
                    field.field_type.clone(),
                );
                let mut infers =
                    rt.define_params_with_set_in_scope(&param_def, BindingScope::StructureField)?;
                rt.attach_known_fact_ids_to_infer_result(&mut infers)?;
                field_definitions.push(SuccessVerifyDefStructFieldDefinitionResult {
                    field_index,
                    binding: field.binding.clone(),
                    field_type: field.field_type.clone(),
                    infers,
                });
            }

            let mut equivalent_facts = Vec::with_capacity(def_struct_stmt.equivalent_facts.len());
            for fact in def_struct_stmt.equivalent_facts.iter() {
                let verify_state = match fact {
                    Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => VerifyState::initial(),
                    _ => VerifyState::final_round(),
                };
                let well_definedness = rt.verify_fact_well_defined_result(fact, &verify_state)?;
                let mut infers = rt
                    .store_fact_without_well_defined_verified_and_without_infer_with_reason(
                        fact.clone(),
                        InferReason::ByDefinition,
                    )?;
                rt.attach_known_fact_ids_to_infer_result(&mut infers)?;
                let fact_id = rt.known_fact_id_for_fact(fact)?;
                equivalent_facts.push(SuccessVerifyLocalFactWellDefinedResult {
                    proposition: fact.clone(),
                    well_definedness: well_definedness
                        .recursive
                        .expect("recursive equivalent-fact WD result"),
                    store: SuccessStoreFactResult {
                        fact: fact.clone(),
                        fact_id,
                        infers,
                    },
                });
            }

            Ok::<SuccessVerifyDefStructFieldScopeResult, RuntimeError>(
                SuccessVerifyDefStructFieldScopeResult {
                    field_definitions,
                    equivalent_facts,
                },
            )
        })?;

        Ok(SuccessVerifyDefStructLocalEnvResult {
            structure_parameter_definition,
            structure_domains,
            field_types,
            field_scope_run_in_local_env,
        })
    }
}
