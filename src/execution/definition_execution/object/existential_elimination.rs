use crate::prelude::*;

impl Runtime {
    pub fn exec_obtain_obj_from_exist_fact(
        &mut self,
        obtain: &ObtainObjFromExistFact,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_obj_from_exist_fact(
            obtain.clone().into(),
            &obtain.equal_tos,
            &obtain.fact,
            obtain.line_file.clone(),
        )
    }

    pub fn exec_obtain_obj_from_atomic_fact(
        &mut self,
        obtain: &ObtainObjFromAtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt: Stmt = obtain.clone().into();
        let (definition, source_exist_fact) = self.resolve_obtain_obj_from_atomic_fact(obtain)?;
        self.verify_obj_from_exist_fact_well_definedness(
            stmt.clone(),
            &obtain.equal_tos,
            &source_exist_fact,
        )?;
        let source_result = self.verify_obj_from_atomic_fact_source(
            stmt.clone(),
            obtain,
            &definition,
            &source_exist_fact,
        )?;
        self.finish_exec_obj_from_exist_fact(
            stmt,
            &obtain.equal_tos,
            &source_exist_fact,
            source_result,
            obtain.line_file.clone(),
        )
    }

    pub fn exec_obtain_obj_from_thm(
        &mut self,
        obtain: &ObtainObjFromThm,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt: Stmt = obtain.clone().into();
        let theorem_call = ReleaseThmStmt::new(
            obtain.thm_name.clone(),
            obtain.args.clone(),
            obtain.line_file.clone(),
        );
        let application_result = self
            .run_in_local_env(|rt| rt.exec_release_thm_stmt(&theorem_call))
            .map_err(|cause| exec_stmt_error_with_stmt_and_cause(stmt.clone(), cause))?;
        let (source_exist_fact, application_result) =
            self.extract_obtain_existential_from_theorem_result(stmt.clone(), application_result)?;

        self.verify_obj_from_exist_fact_well_definedness(
            stmt.clone(),
            &obtain.equal_tos,
            &source_exist_fact,
        )?;
        self.finish_exec_obj_from_exist_fact(
            stmt,
            &obtain.equal_tos,
            &source_exist_fact,
            application_result,
            obtain.line_file.clone(),
        )
    }

    pub fn exec_obtain_obj_from_exist_fact_affect_environment_only(
        &mut self,
        obtain: &ObtainObjFromExistFact,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.apply_obj_from_exist_fact_to_environment(
            obtain.clone().into(),
            &obtain.equal_tos,
            &obtain.fact,
            obtain.line_file.clone(),
        )?;
        Ok(
            SuccessDefinitionStmtResult::ObtainObjFromExistFact(Box::new(
                SuccessObtainObjFromExistFactResult {
                    statement: obtain.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            ))
            .into(),
        )
    }

    pub fn exec_obtain_obj_from_atomic_fact_affect_environment_only(
        &mut self,
        obtain: &ObtainObjFromAtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let (_, source_exist_fact) = self.resolve_obtain_obj_from_atomic_fact(obtain)?;
        let infer_result = self.apply_obj_from_exist_fact_to_environment(
            obtain.clone().into(),
            &obtain.equal_tos,
            &source_exist_fact,
            obtain.line_file.clone(),
        )?;
        Ok(
            SuccessDefinitionStmtResult::ObtainObjFromAtomicFact(Box::new(
                SuccessObtainObjFromAtomicFactResult {
                    statement: obtain.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            ))
            .into(),
        )
    }

    pub fn exec_obtain_obj_from_thm_affect_environment_only(
        &mut self,
        obtain: &ObtainObjFromThm,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt: Stmt = obtain.clone().into();
        let theorem_call = ReleaseThmStmt::new(
            obtain.thm_name.clone(),
            obtain.args.clone(),
            obtain.line_file.clone(),
        );
        let application_result = self
            .run_in_local_env(|rt| rt.exec_release_thm_stmt_affect_environment_only(&theorem_call))
            .map_err(|cause| exec_stmt_error_with_stmt_and_cause(stmt.clone(), cause))?;
        let (source_exist_fact, _) =
            self.extract_obtain_existential_from_theorem_result(stmt.clone(), application_result)?;
        let infer_result = self.apply_obj_from_exist_fact_to_environment(
            stmt.clone(),
            &obtain.equal_tos,
            &source_exist_fact,
            obtain.line_file.clone(),
        )?;
        Ok(
            SuccessDefinitionStmtResult::ObtainObjFromThm(Box::new(
                SuccessObtainObjFromThmResult {
                    statement: obtain.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            ))
            .into(),
        )
    }

    /// Recover the exact direct theorem conclusion selected by the existing
    /// `release thm` executor. The theorem application result is returned intact so
    /// it remains the sole proof source retained by existential elimination.
    fn extract_obtain_existential_from_theorem_result(
        &self,
        stmt: Stmt,
        application_result: StmtResult,
    ) -> Result<(ExistFactEnum, StmtResult), RuntimeError> {
        let extracted = (|| -> Result<ExistFactEnum, String> {
            let success = application_result.non_factual_success().ok_or_else(|| {
                "obtain from thm: theorem application did not return a statement success"
                    .to_string()
            })?;
            let SuccessStmtResult::ReleaseThmStmt(result) = success else {
                return Err(
                    "obtain from thm: theorem application did not retain theorem verification evidence"
                        .to_string(),
                );
            };
            let Some(verification) = result.verification.as_ref() else {
                return Err(
                    "obtain from thm: theorem application did not retain theorem verification evidence"
                        .to_string(),
                );
            };
            if verification.direct_conclusions.len() != 1 {
                return Err(format!(
                    "obtain from thm `{}` requires exactly one direct theorem conclusion, got {}",
                    verification.theorem,
                    verification.direct_conclusions.len()
                ));
            }
            let Fact::ExistFact(exist_fact) = &verification.direct_conclusions[0] else {
                return Err(format!(
                    "obtain from thm `{}` requires its sole direct conclusion to be `exist` or `exist!`",
                    verification.theorem
                ));
            };
            if exist_fact.is_not_exist() {
                return Err(format!(
                    "obtain from thm `{}` cannot eliminate a `not exist` conclusion",
                    verification.theorem
                ));
            }
            Ok(exist_fact.clone())
        })();

        match extracted {
            Ok(exist_fact) => Ok((exist_fact, application_result)),
            Err(message) => Err(short_exec_error(
                stmt,
                message,
                None,
                vec![application_result],
            )),
        }
    }

    pub fn exec_have_obj_by_exist_facts_stmt(
        &mut self,
        stmt: &HaveObjByExistFactsStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let body = ExistentialSpec::new(
            stmt.param_def.clone(),
            stmt.facts.clone(),
            stmt.line_file.clone(),
        )
        .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        let exist_fact = ExistFactEnum::ExistFact(body);
        let equal_to_bindings = stmt.param_def.collect_param_bindings();
        self.exec_obj_from_exist_fact(
            stmt.clone().into(),
            &equal_to_bindings,
            &exist_fact,
            stmt.line_file.clone(),
        )
    }

    pub fn exec_have_obj_by_exist_facts_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveObjByExistFactsStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let body = ExistentialSpec::new(
            stmt.param_def.clone(),
            stmt.facts.clone(),
            stmt.line_file.clone(),
        )
        .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        let exist_fact = ExistFactEnum::ExistFact(body);
        let equal_to_bindings = stmt.param_def.collect_param_bindings();
        let infer_result = self.apply_obj_from_exist_fact_to_environment(
            stmt.clone().into(),
            &equal_to_bindings,
            &exist_fact,
            stmt.line_file.clone(),
        )?;
        Ok(
            SuccessDefinitionStmtResult::HaveObjByExistFactsStmt(Box::new(
                SuccessHaveObjByExistFactsStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            ))
            .into(),
        )
    }

    fn exec_obj_from_exist_fact(
        &mut self,
        stmt: Stmt,
        defined_bindings: &[SymbolBinding],
        source_exist_fact: &ExistFactEnum,
        line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_from_exist_fact_well_definedness(
            stmt.clone(),
            defined_bindings,
            source_exist_fact,
        )?;
        let source_result =
            self.verify_obj_from_exist_fact_source(stmt.clone(), source_exist_fact)?;
        self.finish_exec_obj_from_exist_fact(
            stmt,
            defined_bindings,
            source_exist_fact,
            source_result,
            line_file,
        )
    }

    fn finish_exec_obj_from_exist_fact(
        &mut self,
        stmt: Stmt,
        defined_bindings: &[SymbolBinding],
        source_exist_fact: &ExistFactEnum,
        source_result: StmtResult,
        line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.apply_obj_from_exist_fact_to_environment(
            stmt.clone(),
            defined_bindings,
            source_exist_fact,
            line_file.clone(),
        )?;
        let elimination_verification = self.existential_elimination_verification_result(
            &stmt,
            defined_bindings,
            source_exist_fact,
            source_result,
            line_file,
        )?;

        let common = SuccessStmtCommonResult::new(infer_result);
        let ir = match stmt {
            Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(statement)) => {
                SuccessDefinitionStmtResult::HaveObjByExistFactsStmt(Box::new(
                    SuccessHaveObjByExistFactsStmtResult {
                        statement,
                        common,
                        verification: Some(elimination_verification),
                    },
                ))
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromExistFact(statement)) => {
                SuccessDefinitionStmtResult::ObtainObjFromExistFact(Box::new(
                    SuccessObtainObjFromExistFactResult {
                        statement,
                        common,
                        verification: Some(elimination_verification),
                    },
                ))
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromAtomicFact(statement)) => {
                SuccessDefinitionStmtResult::ObtainObjFromAtomicFact(Box::new(
                    SuccessObtainObjFromAtomicFactResult {
                        statement,
                        common,
                        verification: Some(elimination_verification),
                    },
                ))
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromThm(statement)) => {
                SuccessDefinitionStmtResult::ObtainObjFromThm(Box::new(
                    SuccessObtainObjFromThmResult {
                        statement,
                        common,
                        verification: Some(elimination_verification),
                    },
                ))
            }
            _ => unreachable!("existential elimination must retain its exact object statement"),
        };
        Ok(ir.into())
    }

    /// Mathematical contract: existential elimination introduces exactly one
    /// fresh object name for each existential parameter, and the complete
    /// existential formula is meaningful before those witnesses enter scope.
    fn verify_obj_from_exist_fact_well_definedness(
        &mut self,
        stmt: Stmt,
        defined_bindings: &[SymbolBinding],
        source_exist_fact: &ExistFactEnum,
    ) -> Result<(), RuntimeError> {
        if source_exist_fact.typed_parameters().number_of_params() != defined_bindings.len() {
            return Err(short_exec_error(
                stmt.clone(),
                "existential elimination: number of parameters does not match number of obtained objects"
                    .to_string(),
                None,
                vec![],
            ));
        }

        self.run_in_local_env(|rt| {
            rt.verify_exist_fact_well_defined(source_exist_fact, &VerifyState::initial())
                .map_err(|well_defined_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), well_defined_error)
                })?;
            for binding in defined_bindings {
                rt.store_parameter_binding(binding, BindingScope::DefinitionBinding)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
            }
            Ok(())
        })
    }

    fn verify_obj_from_exist_fact_source(
        &mut self,
        stmt: Stmt,
        source_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        let verify_state = VerifyState::initial();
        let result = self
            .verify_exist_fact(source_exist_fact, &verify_state)
            .map_err(|verify_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone(), verify_error)
            })?;
        if result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone(),
                "existential elimination: source existence fact is not verified".to_string(),
                None,
                vec![],
            ));
        }

        Ok(result)
    }

    fn verify_obj_from_atomic_fact_source(
        &mut self,
        stmt: Stmt,
        obtain: &ObtainObjFromAtomicFact,
        definition: &DefPropStmt,
        source_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        let source_atomic: AtomicFact = obtain.fact.clone().into();
        let source_result = self
            .verify_atomic_fact(&source_atomic, &VerifyState::initial())
            .map_err(|verify_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone(), verify_error)
            })?;
        if source_result.is_unknown() {
            return Err(short_exec_error(
                stmt,
                format!("obtain: source prop `{}` is not verified", obtain.fact),
                None,
                vec![],
            ));
        }

        let projection_result =
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                source_exist_fact.clone().into(),
                format!(
                    "existential projection from prop definition `{}`",
                    definition.name
                ),
                BuiltinRuleEvidence::DefinitionProjection(
                    DefinitionProjectionBuiltinRuleEvidence::new(
                        obtain.fact.clone(),
                        definition.clone(),
                    ),
                ),
                vec![source_result],
            );
        Ok(projection_result.into())
    }

    /// Resolve the concrete definition at execution time; the statement keeps
    /// only the source atomic fact and never caches parser-time definition data.
    fn resolve_obtain_obj_from_atomic_fact(
        &self,
        stmt: &ObtainObjFromAtomicFact,
    ) -> Result<(DefPropStmt, ExistFactEnum), RuntimeError> {
        let source_stmt: Stmt = stmt.clone().into();
        let predicate_name = stmt.fact.predicate.to_string();
        if self
            .get_abstract_prop_definition_by_name(&predicate_name)
            .is_some()
        {
            return Err(short_exec_error(
                source_stmt,
                format!(
                    "obtain requires a concrete `prop`; `{}` is an `abstract_prop`",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        let definition = self
            .get_active_prop_definition_by_name(&predicate_name)
            .ok_or_else(|| {
                short_exec_error(
                    source_stmt.clone(),
                    format!(
                        "obtain could not find a concrete prop definition for `{}`",
                        predicate_name
                    ),
                    None,
                    vec![],
                )
            })?;
        let existential = self
            .instantiate_existential_prop_definition(&stmt.fact, &definition, &stmt.line_file)
            .map_err(|cause| exec_stmt_error_with_stmt_and_cause(source_stmt, cause))?;
        Ok((definition, existential))
    }

    fn apply_obj_from_exist_fact_to_environment(
        &mut self,
        stmt: Stmt,
        defined_bindings: &[SymbolBinding],
        source_exist_fact: &ExistFactEnum,
        line_file: LineFile,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let new_obj_names_as_identifier_objs: Vec<Obj> = defined_bindings
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect();

        let param_to_obj_map = source_exist_fact
            .typed_parameters()
            .param_defs_and_args_to_param_to_arg_map(new_obj_names_as_identifier_objs.as_slice());
        let mut binding_index = 0;
        for group in source_exist_fact.typed_parameters().groups.iter() {
            let instantiated_type = self.inst_param_type(
                &group.param_type,
                &param_to_obj_map,
                SubstitutionMode::Exact,
            )?;
            for _ in group.params.iter() {
                self.store_typed_parameter_binding(
                    &defined_bindings[binding_index],
                    BindingScope::DefinitionBinding,
                    &instantiated_type,
                )?;
                binding_index += 1;
            }
        }

        let mut infer_result = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers_with_reason(
                source_exist_fact.typed_parameters(),
                &new_obj_names_as_identifier_objs,
                line_file.clone(),
                SubstitutionMode::Exact,
                InferReason::ExistElimination,
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;

        let body_fact_verify_state = VerifyState::initial();
        for fact in source_exist_fact.facts().iter() {
            let instantiated_fact = self
                .inst_quantifier_free_fact(fact, &param_to_obj_map, SubstitutionMode::Exact, None)
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

        if source_exist_fact.is_exist_unique() {
            let uniqueness_forall = self
                .build_exist_unique_uniqueness_forall_fact(source_exist_fact)
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
        _stmt: &Stmt,
        equal_tos: &[SymbolBinding],
        exist_fact: &ExistFactEnum,
        source_result: StmtResult,
        line_file: LineFile,
    ) -> Result<SuccessVerifyExistentialEliminationResult, RuntimeError> {
        let witnesses = equal_tos
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect::<Vec<Obj>>();
        let instantiated_types = self.inst_param_def_with_type_one_by_one(
            exist_fact.typed_parameters(),
            &witnesses,
            SubstitutionMode::Exact,
        )?;
        let flat_types = exist_fact
            .typed_parameters()
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
            .typed_parameters()
            .param_defs_and_args_to_param_to_arg_map(&witnesses);
        let instantiated_body_facts = exist_fact
            .facts()
            .iter()
            .map(|fact| {
                self.inst_quantifier_free_fact(
                    fact,
                    &param_to_obj_map,
                    SubstitutionMode::Exact,
                    None,
                )
                .map(QuantifierFreeFact::to_fact)
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;

        Ok(SuccessVerifyExistentialEliminationResult::new(
            source_result,
            exist_fact.clone(),
            witness_type_facts,
            instantiated_body_facts,
            exist_fact.is_exist_unique(),
        ))
    }
}
