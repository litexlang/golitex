use crate::prelude::*;

impl Runtime {
    pub fn exec_have_exist_obj_stmt(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact = self.resolve_have_by_exist_source(have_exist_obj_stmt)?;
        self.exec_have_exist_obj_core(
            have_exist_obj_stmt.clone().into(),
            &have_exist_obj_stmt.equal_tos,
            &have_exist_obj_stmt.equal_to_bindings,
            &exist_fact,
            have_exist_obj_stmt.existential_prop_source.as_ref(),
            have_exist_obj_stmt.line_file.clone(),
        )
    }

    pub(crate) fn exec_have_exist_obj_stmt_affect_environment_only(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact = self.resolve_have_by_exist_source(have_exist_obj_stmt)?;
        let infer_result = self.exec_have_exist_obj_stmt_affect_environment(
            have_exist_obj_stmt.clone().into(),
            &have_exist_obj_stmt.equal_to_bindings,
            &exist_fact,
            have_exist_obj_stmt.line_file.clone(),
        )?;
        Ok(
            NonFactualStmtSuccess::new(have_exist_obj_stmt.clone().into(), infer_result, vec![])
                .into(),
        )
    }

    pub fn exec_have_obj_by_exist_facts_stmt(
        &mut self,
        stmt: &HaveObjByExistFactsStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let body = ExistFactBody::new(
            stmt.param_def.clone(),
            stmt.facts.clone(),
            stmt.line_file.clone(),
        )
        .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        let exist_fact = ExistFactEnum::ExistFact(body);
        let equal_tos = stmt.param_def.collect_param_names();
        let equal_to_bindings = stmt.param_def.collect_param_bindings();
        self.exec_have_exist_obj_core(
            stmt.clone().into(),
            &equal_tos,
            &equal_to_bindings,
            &exist_fact,
            None,
            stmt.line_file.clone(),
        )
    }

    pub(crate) fn exec_have_obj_by_exist_facts_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveObjByExistFactsStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let body = ExistFactBody::new(
            stmt.param_def.clone(),
            stmt.facts.clone(),
            stmt.line_file.clone(),
        )
        .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        let exist_fact = ExistFactEnum::ExistFact(body);
        let equal_to_bindings = stmt.param_def.collect_param_bindings();
        let infer_result = self.exec_have_exist_obj_stmt_affect_environment(
            stmt.clone().into(),
            &equal_to_bindings,
            &exist_fact,
            stmt.line_file.clone(),
        )?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_have_exist_obj_core(
        &mut self,
        stmt: Stmt,
        equal_tos: &[String],
        equal_to_bindings: &[SymbolBinding],
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
        existential_prop_source: Option<&ExistentialPropSource>,
        line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_exist_obj_stmt_verify_well_definedness(
            stmt.clone(),
            equal_tos,
            equal_to_bindings,
            exist_fact_in_have_obj_stmt,
        )?;
        let inside_results = self.exec_have_exist_obj_stmt_verify_process(
            stmt.clone(),
            exist_fact_in_have_obj_stmt,
            existential_prop_source,
        )?;
        let infer_result = self.exec_have_exist_obj_stmt_affect_environment(
            stmt.clone(),
            equal_to_bindings,
            exist_fact_in_have_obj_stmt,
            line_file.clone(),
        )?;
        let elimination_verification = self.existential_elimination_verification_result(
            &stmt,
            equal_to_bindings,
            exist_fact_in_have_obj_stmt,
            &inside_results,
            line_file,
        )?;

        let mut success = NonFactualStmtSuccess::new(stmt, infer_result, inside_results);
        success.existential_elimination_verification = Some(elimination_verification);
        Ok(success.into())
    }

    /// Mathematical contract: existential elimination introduces exactly one
    /// fresh object name for each existential parameter, and the complete
    /// existential formula is meaningful before those witnesses enter scope.
    fn exec_have_exist_obj_stmt_verify_well_definedness(
        &mut self,
        stmt: Stmt,
        equal_tos: &[String],
        equal_to_bindings: &[SymbolBinding],
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
    ) -> Result<(), RuntimeError> {
        if exist_fact_in_have_obj_stmt
            .params_def_with_type()
            .number_of_params()
            != equal_tos.len()
        {
            return Err(short_exec_error(
                stmt.clone(),
                "have_exist_obj_stmt: number of params in exist does not match number of given objs"
                    .to_string(),
                None,
                vec![],
            ));
        }

        self.run_in_local_env(|rt| {
            rt.verify_exist_fact_well_defined(
                exist_fact_in_have_obj_stmt,
                &UseContextVerifyState::new(0, false),
            )
            .map_err(|well_defined_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone(), well_defined_error)
            })?;
            for binding in equal_to_bindings {
                rt.store_parameter_binding(binding, ParamObjType::Identifier)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
            }
            Ok(())
        })
    }

    fn exec_have_exist_obj_stmt_verify_process(
        &mut self,
        stmt: Stmt,
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
        existential_prop_source: Option<&ExistentialPropSource>,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let verify_state = UseContextVerifyState::new(0, false);

        if let Some(source) = existential_prop_source {
            let source_atomic: AtomicFact = source.fact.clone().into();
            let source_result = self
                .verify_atomic_fact(&source_atomic, &verify_state)
                .map_err(|verify_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), verify_error)
                })?;
            if source_result.is_unknown() {
                return Err(short_exec_error(
                    stmt,
                    format!("obtain: source prop `{}` is not verified", source.fact),
                    None,
                    vec![],
                ));
            }

            let projection_result =
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    exist_fact_in_have_obj_stmt.clone().into(),
                    format!(
                        "existential projection from prop definition `{}`",
                        source.definition.name
                    ),
                    vec![source_result],
                );
            return Ok(vec![projection_result.into()]);
        }

        let result = self
            .verify_exist_fact(exist_fact_in_have_obj_stmt, &verify_state)
            .map_err(|verify_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone(), verify_error)
            })?;
        if result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone(),
                "have_exist_obj_stmt: exist fact is not verified".to_string(),
                None,
                vec![],
            ));
        }

        Ok(vec![result])
    }

    /// Resolve the existential used by elimination. For the shorthand source,
    /// this repeats the definition-shape and substitution checks at execution
    /// time; the kernel does not rely on the parser's cached expansion.
    fn resolve_have_by_exist_source(
        &self,
        stmt: &HaveByExistStmt,
    ) -> Result<ExistFactEnum, RuntimeError> {
        let Some(source) = stmt.existential_prop_source.as_ref() else {
            return Ok(stmt.exist_fact_in_have_obj_st.clone());
        };

        let predicate_name = source.fact.predicate.to_string();
        let local_predicate_name = predicate_name
            .rsplit_once(MOD_SIGN)
            .map(|(_, local_name)| local_name)
            .unwrap_or(predicate_name.as_str());
        if local_predicate_name != source.definition.name {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "obtain: source prop `{}` does not match retained definition `{}`",
                    predicate_name, source.definition.name
                ),
                None,
                vec![],
            ));
        }
        if source.definition.iff_facts.len() != 1 {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "obtain: prop `{}` must have exactly one definition clause",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        let Fact::ExistFact(definition_exist_fact) = &source.definition.iff_facts[0] else {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "obtain: the sole definition clause of `{}` must be `exist` or `exist!`",
                    predicate_name
                ),
                None,
                vec![],
            ));
        };
        if definition_exist_fact.is_not_exist() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "obtain: the definition clause of `{}` is `not exist`",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }

        let param_to_arg_map = self
            .params_to_arg_map(&source.definition.params_def_with_type, &source.fact.body)
            .map_err(|cause| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), cause))?;
        self.inst_exist_fact(
            definition_exist_fact,
            &param_to_arg_map,
            ParamObjType::DefHeader,
            Some(&stmt.line_file),
        )
        .map_err(|cause| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), cause))
    }

    fn exec_have_exist_obj_stmt_affect_environment(
        &mut self,
        stmt: Stmt,
        equal_to_bindings: &[SymbolBinding],
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
        line_file: LineFile,
    ) -> Result<InferResult, RuntimeError> {
        for binding in equal_to_bindings {
            self.store_parameter_binding(binding, ParamObjType::Identifier)?;
        }

        let new_obj_names_as_identifier_objs: Vec<Obj> = equal_to_bindings
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect();

        let mut infer_result = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers_with_reason(
                exist_fact_in_have_obj_stmt.params_def_with_type(),
                &new_obj_names_as_identifier_objs,
                line_file.clone(),
                ParamObjType::Exist,
                InferReason::ExistElimination,
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;

        let param_to_obj_map = exist_fact_in_have_obj_stmt
            .params_def_with_type()
            .param_defs_and_args_to_param_to_arg_map(new_obj_names_as_identifier_objs.as_slice());

        let body_fact_verify_state = UseContextVerifyState::new(0, false);
        for fact in exist_fact_in_have_obj_stmt.facts().iter() {
            let instantiated_fact = self
                .inst_exist_body_fact(fact, &param_to_obj_map, ParamObjType::Exist, None)
                .map_err(|runtime_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), runtime_error)
                })?
                .to_fact();
            let fact_infer_result = self
                .store_with_well_defined_verification_and_infer_with_reason(
                    instantiated_fact,
                    &body_fact_verify_state,
                    InferReason::ExistElimination,
                )
                .map_err(|store_fact_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), store_fact_error)
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }

        if exist_fact_in_have_obj_stmt.is_exist_unique() {
            let uniqueness_forall = self
                .build_exist_unique_uniqueness_forall_fact(exist_fact_in_have_obj_stmt)
                .map_err(|runtime_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), runtime_error)
                })?;
            let uniqueness_infer_result = self
                .store_fact_without_forall_coverage_check_and_infer(uniqueness_forall.into())
                .map_err(|store_fact_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), store_fact_error)
                })?;
            infer_result.new_infer_result_inside(uniqueness_infer_result);
        }

        Ok(infer_result)
    }

    fn existential_elimination_verification_result(
        &self,
        stmt: &Stmt,
        equal_to_bindings: &[SymbolBinding],
        exist_fact: &ExistFactEnum,
        inside_results: &[StmtResult],
        line_file: LineFile,
    ) -> Result<ExistentialEliminationVerificationResult, RuntimeError> {
        if inside_results.len() != 1 {
            return Err(exec_stmt_error_with_stmt_and_cause(
                stmt.clone(),
                RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                    "existential elimination did not retain exactly one source proof".to_string(),
                ))),
            ));
        }

        let witnesses = equal_to_bindings
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect::<Vec<Obj>>();
        let instantiated_types = self.inst_param_def_with_type_one_by_one(
            exist_fact.params_def_with_type(),
            &witnesses,
            ParamObjType::Exist,
        )?;
        let flat_types = exist_fact
            .params_def_with_type()
            .flat_instantiated_types_for_args(&instantiated_types);
        let witness_type_facts = witnesses
            .iter()
            .cloned()
            .zip(flat_types.iter())
            .map(|(witness, param_type)| match param_type {
                ParamType::Set(_) => IsSetFact::new(witness, line_file.clone()).into(),
                ParamType::NonemptySet(_) => {
                    IsNonemptySetFact::new(witness, line_file.clone()).into()
                }
                ParamType::FiniteSet(_) => IsFiniteSetFact::new(witness, line_file.clone()).into(),
                ParamType::Obj(carrier) => {
                    InFact::new(witness, carrier.clone(), line_file.clone()).into()
                }
            })
            .collect::<Vec<Fact>>();

        let param_to_obj_map = exist_fact
            .params_def_with_type()
            .param_defs_and_args_to_param_to_arg_map(&witnesses);
        let instantiated_body_facts = exist_fact
            .facts()
            .iter()
            .map(|fact| {
                self.inst_exist_body_fact(fact, &param_to_obj_map, ParamObjType::Exist, None)
                    .map(ExistBodyFact::to_fact)
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;

        Ok(ExistentialEliminationVerificationResult::new(
            0,
            witness_type_facts,
            instantiated_body_facts,
            exist_fact.is_exist_unique(),
        ))
    }
}
