use crate::prelude::*;

impl Runtime {
    pub fn exec_release_thm_stmt(
        &mut self,
        stmt: &ReleaseThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(result) = self.exec_builtin_thm_stmt(stmt)? {
            return Ok(result);
        }
        let thm_name = stmt.name.to_string();
        let forall_fact = self
            .get_thm_or_axiom_forall_fact_by_name(&thm_name)
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("release thm: theorem `{}` is not defined", stmt.name),
                    None,
                    vec![],
                )
            })?;
        let source_fact_id = self.known_fact_id_for_fact(&forall_fact.clone().into())?;

        let verify_state = VerifyState::initial();
        let arg_type_result = self
            .verify_args_satisfy_param_def_flat_types(
                &forall_fact.typed_parameters,
                &stmt.args,
                &verify_state,
                SubstitutionMode::Exact,
            )
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "release thm `{}`: arguments do not match theorem parameters",
                        stmt.name
                    ),
                    Some(e),
                    vec![],
                )
            })?;
        let argument_verification = match arg_type_result {
            VerifyArgsSatisfyParamDefResult::Success(result) => *result,
            VerifyArgsSatisfyParamDefResult::Unknown(result) => {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "release thm `{}`: could not verify argument parameter types",
                        stmt.name
                    ),
                    None,
                    vec![*result.cause],
                ));
            }
        };

        let param_to_arg_map = forall_fact
            .typed_parameters
            .param_defs_and_args_to_param_to_arg_map(&stmt.args);

        let mut infer_result = SuccessInferResult::new();
        infer_result.new_infer_result_inside(argument_verification.infers.clone());
        let mut domain_checks = Vec::new();
        let mut domain_facts = Vec::new();
        for dom_fact in forall_fact.dom_facts.iter() {
            let instantiated_dom = self
                .inst_fact(
                    dom_fact,
                    &param_to_arg_map,
                    SubstitutionMode::Theorem,
                    Some(stmt.line_file.clone()),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "release thm `{}`: failed to instantiate domain fact `{}`",
                            stmt.name, dom_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            let dom_result = self
                .verify_fact_allow_unknown(&instantiated_dom, &verify_state)
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "release thm `{}`: failed to verify domain fact `{}`",
                            stmt.name, instantiated_dom
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            if dom_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "release thm `{}`: domain fact `{}` is not verified",
                        stmt.name, instantiated_dom
                    ),
                    None,
                    vec![dom_result],
                ));
            }
            Self::merge_stmt_result_infers(&mut infer_result, &dom_result);
            domain_facts.push(instantiated_dom);
            domain_checks.push(dom_result);
        }

        let mut direct_conclusions = Vec::new();
        for then_fact in forall_fact.then_facts.iter() {
            let instantiated_then = self
                .inst_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &param_to_arg_map,
                    SubstitutionMode::Theorem,
                    Some(&stmt.line_file),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "release thm `{}`: failed to instantiate then fact `{}`",
                            stmt.name, then_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            direct_conclusions.push(instantiated_then.clone().to_fact());
            infer_result.new_infer_result_inside(
                self.store_exist_or_and_chain_atomic_fact_with_well_defined_verification_and_infer_with_reason(
                    &instantiated_then,
                    &verify_state,
                    InferReason::TheoremInstantiation,
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "release thm `{}`: failed to store instantiated then fact `{}`",
                            stmt.name, instantiated_then
                        ),
                        Some(e),
                        vec![],
                    )
                })?,
            );
        }

        let theorem_verification = SuccessVerifyTheoremApplicationResult::new(
            thm_name,
            source_fact_id,
            stmt.args.clone(),
            domain_facts,
            direct_conclusions,
            Some(argument_verification),
            domain_checks,
        );
        Ok(
            SuccessStmtResult::ReleaseThmStmt(Box::new(SuccessReleaseThmStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(theorem_verification),
            }))
            .into(),
        )
    }

    pub fn exec_release_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &ReleaseThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(result) = self.exec_builtin_thm_stmt_affect_environment_only(stmt)? {
            return Ok(result);
        }
        let thm_name = stmt.name.to_string();
        let forall_fact = self
            .get_thm_or_axiom_forall_fact_by_name(&thm_name)
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("release thm: theorem `{}` is not defined", stmt.name),
                    None,
                    vec![],
                )
            })?;
        let source_fact_id = self.known_fact_id_for_fact(&forall_fact.clone().into())?;

        let param_to_arg_map = forall_fact
            .typed_parameters
            .param_defs_and_args_to_param_to_arg_map(&stmt.args);

        let mut infer_result = SuccessInferResult::new();
        let mut direct_conclusions = Vec::new();
        for then_fact in forall_fact.then_facts.iter() {
            let instantiated_then = self
                .inst_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &param_to_arg_map,
                    SubstitutionMode::Theorem,
                    Some(&stmt.line_file),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "release thm `{}`: failed to instantiate then fact `{}`",
                            stmt.name, then_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            direct_conclusions.push(instantiated_then.clone().to_fact());
            infer_result.new_infer_result_inside(
                self.store_trusted_fact_and_infer_with_reason(
                    instantiated_then.clone().to_fact(),
                    InferReason::TheoremInstantiation,
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "release thm `{}`: failed to store instantiated then fact `{}`",
                            stmt.name, instantiated_then
                        ),
                        Some(e),
                        vec![],
                    )
                })?,
            );
        }

        let theorem_verification = SuccessVerifyTheoremApplicationResult::new(
            thm_name,
            source_fact_id,
            stmt.args.clone(),
            vec![],
            direct_conclusions,
            None,
            Vec::new(),
        );
        Ok(
            SuccessStmtResult::ReleaseThmStmt(Box::new(SuccessReleaseThmStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(theorem_verification),
            }))
            .into(),
        )
    }

    pub fn exec_by_thm_stmt(&mut self, stmt: &ByThmStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_by_thm_stmt_select_atomic_fact(stmt)
    }

    pub fn exec_by_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_by_thm_stmt_select_atomic_fact_affect_environment_only(stmt)
    }

    fn exec_by_thm_stmt_select_atomic_fact(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let selected_fact = stmt.selected_fact.clone();
        let verify_state = VerifyState::initial();
        self.verify_atomic_fact_well_defined(&selected_fact, &verify_state)
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: selected fact `{}` is not well-defined in the parent environment",
                        stmt.name, selected_fact
                    ),
                    Some(error),
                    vec![],
                )
            })?;

        let expanded_stmt =
            ReleaseThmStmt::new(stmt.name.clone(), stmt.args.clone(), stmt.line_file.clone());
        let (expanded_result, target_result) = self.run_in_local_env(|rt| {
            let mut expanded_result = rt.exec_release_thm_stmt(&expanded_stmt).map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: temporary theorem application failed",
                        stmt.name
                    ),
                    Some(error),
                    vec![],
                )
            })?;
            rt.attach_known_fact_ids_to_stmt_result(&mut expanded_result)?;
            let mut target_result = rt
                .verify_atomic_fact(
                    &selected_fact,
                    &verify_state.with_well_definedness_verified(),
                )
                .map_err(|error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to verify selected fact `{}` after theorem application",
                            stmt.name, selected_fact
                        ),
                        Some(error),
                        vec![],
                    )
                })?;
            if target_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: selected fact `{}` is not verified after theorem application",
                        stmt.name, selected_fact
                    ),
                    None,
                    vec![target_result],
                ));
            }
            rt.attach_known_fact_ids_to_stmt_result(&mut target_result)?;
            Ok((expanded_result, target_result))
        })?;

        if !matches!(
            &expanded_result,
            StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(result))
                if result.verification.is_some()
        ) {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by thm: theorem application did not retain verified release evidence".to_string(),
                None,
                vec![expanded_result],
            ));
        }

        let infer_result = self
            .run_in_local_env_and_commit(|rt| {
                rt.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    selected_fact.clone(),
                    ByThmStmt::selected_fact_store_reason(),
                )
            })
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: failed to store selected fact `{}`",
                        stmt.name, selected_fact
                    ),
                    Some(error),
                    vec![],
                )
            })?;

        Ok(
            SuccessByStmtResult::ByThmStmt(Box::new(SuccessByThmStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(SuccessVerifyByTheoremSelectionResult::new(
                    expanded_result,
                    selected_fact,
                    target_result,
                )),
            }))
            .into(),
        )
    }

    fn exec_by_thm_stmt_select_atomic_fact_affect_environment_only(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let selected_fact = stmt.selected_fact.clone();
        let expanded_stmt =
            ReleaseThmStmt::new(stmt.name.clone(), stmt.args.clone(), stmt.line_file.clone());
        self.run_in_local_env(|rt| {
            rt.exec_release_thm_stmt_affect_environment_only(&expanded_stmt)
                .map_err(|error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: temporary theorem application failed",
                            stmt.name
                        ),
                        Some(error),
                        vec![],
                    )
                })?;
            Ok::<_, RuntimeError>(())
        })?;

        let infer_result = self
            .run_in_local_env_and_commit(|rt| {
                rt.store_trusted_fact_and_infer_with_reason(
                    selected_fact.clone().into(),
                    InferReason::Other(ByThmStmt::selected_fact_store_reason().to_string()),
                )
            })
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: failed to store selected fact `{}`",
                        stmt.name, selected_fact
                    ),
                    Some(error),
                    vec![],
                )
            })?;

        Ok(
            SuccessByStmtResult::ByThmStmt(Box::new(SuccessByThmStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            }))
            .into(),
        )
    }

    fn merge_stmt_result_infers(infer_result: &mut SuccessInferResult, stmt_result: &StmtResult) {
        infer_result.new_infer_result_inside(stmt_result.infer_result());
    }

    fn exec_builtin_thm_stmt(
        &mut self,
        stmt: &ReleaseThmStmt,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        self.exec_builtin_thm_stmt_impl(stmt, true)
    }

    fn exec_builtin_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &ReleaseThmStmt,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        self.exec_builtin_thm_stmt_impl(stmt, false)
    }

    fn exec_builtin_thm_stmt_impl(
        &mut self,
        stmt: &ReleaseThmStmt,
        verify_requirements: bool,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let name = match &stmt.name {
            AtomicName::WithoutMod(name) if is_builtin_theorem_name(name) => name.as_str(),
            AtomicName::WithMod(_, local_name) if is_builtin_theorem_name(local_name) => {
                return Err(builtin_thm_exec_error(
                    stmt,
                    format!(
                        "builtin theorem `{}` is a reserved bare global name and cannot be qualified",
                        local_name
                    ),
                    vec![],
                ));
            }
            _ => return Ok(None),
        };
        let theorem_id = BuiltinTheoremId::from_name(name)
            .expect("reserved builtin theorem name has a typed identity");

        macro_rules! require_arity {
            ($expected:expr) => {
                if stmt.args.len() != $expected {
                    return Err(builtin_thm_exec_error(
                        stmt,
                        format!(
                            "builtin theorem `{}` expects {} argument(s), but got {}",
                            name,
                            $expected,
                            stmt.args.len()
                        ),
                        vec![],
                    ));
                }
            };
        }

        let verify_state = VerifyState::initial();
        if name == "real_cauchy_sequence_converges" {
            require_arity!(1);
            validate_real_sequence_completeness_definition_contract(self, stmt)?;

            // These predicates were selected from the active local definition
            // registry by the exact contract check above. Keep the facts bare:
            // isolated sources legitimately have an empty module name, for
            // which manufacturing `$::predicate` is neither resolvable nor
            // equivalent to the local declaration.
            let predicate_name = |local_name: &str| AtomicName::WithoutMod(local_name.to_string());
            let real_sequence: AtomicFact = InFact::new(
                stmt.args[0].clone(),
                SeqSet::new(StandardSet::R.into()).into(),
                stmt.line_file.clone(),
            )
            .into();
            let cauchy: AtomicFact = NormalAtomicFact::new(
                predicate_name("is_cauchy_sequence"),
                vec![stmt.args[0].clone()],
                stmt.line_file.clone(),
            )
            .into();
            let conclusion: AtomicFact = NormalAtomicFact::new(
                predicate_name("is_convergent_sequence"),
                vec![stmt.args[0].clone()],
                stmt.line_file.clone(),
            )
            .into();

            let mut requirement_facts = Vec::new();
            let mut requirement_roles = Vec::new();
            let mut inside_results = Vec::new();
            let conclusion_well_definedness =
                if verify_requirements {
                    for (requirement, role) in [
                        (
                            real_sequence,
                            BuiltinTheoremRequirementRole::ArgumentIsRealSequence,
                        ),
                        (
                            cauchy,
                            BuiltinTheoremRequirementRole::SequenceSatisfiesCauchyDefinition,
                        ),
                    ] {
                        self.verify_atomic_fact_well_defined(&requirement, &verify_state)?;
                        let result = self.verify_atomic_fact(&requirement, &verify_state)?;
                        if !result.is_success() {
                            return Err(builtin_thm_exec_error(
                                stmt,
                                format!(
                                "builtin theorem `real_cauchy_sequence_converges` requires that {}",
                                role.as_str()
                            ),
                                vec![result],
                            ));
                        }
                        requirement_facts.push(requirement.into());
                        requirement_roles.push(role);
                        inside_results.push(result);
                    }
                    Some(self.verify_fact_well_defined_result(
                        &conclusion.clone().into(),
                        &verify_state,
                    )?)
                } else {
                    None
                };

            let store_reason = InferReason::Other(format!("builtin theorem `{}`", name));
            let infer_result = if verify_requirements {
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    conclusion.clone(),
                    store_reason.store_reason(),
                )?
            } else {
                self.store_trusted_fact_and_infer_with_reason(
                    conclusion.clone().into(),
                    store_reason,
                )?
            };
            let direct_conclusions = vec![conclusion.into()];
            let verification = match conclusion_well_definedness {
                Some(conclusion_well_definedness) => {
                    SuccessVerifyTheoremApplicationResult::new_builtin_with_conclusion_well_definedness(
                        theorem_id,
                        stmt.args.clone(),
                        requirement_facts,
                        requirement_roles,
                        direct_conclusions,
                        inside_results,
                        conclusion_well_definedness,
                        None,
                    )
                }
                None => SuccessVerifyTheoremApplicationResult::new_builtin(
                    theorem_id,
                    stmt.args.clone(),
                    requirement_facts,
                    requirement_roles,
                    direct_conclusions,
                    inside_results,
                    None,
                ),
            };
            return Ok(Some(
                SuccessStmtResult::ReleaseThmStmt(Box::new(SuccessReleaseThmStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(verification),
                }))
                .into(),
            ));
        }

        if name == "subset_of_finite_set_is_finite" {
            require_arity!(2);

            let conclusion: AtomicFact =
                IsFiniteSetFact::new(stmt.args[0].clone(), stmt.line_file.clone()).into();
            let first_is_set: AtomicFact =
                IsSetFact::new(stmt.args[0].clone(), stmt.line_file.clone()).into();
            let second_is_finite: AtomicFact =
                IsFiniteSetFact::new(stmt.args[1].clone(), stmt.line_file.clone()).into();
            let subset: AtomicFact = SubsetFact::new(
                stmt.args[0].clone(),
                stmt.args[1].clone(),
                stmt.line_file.clone(),
            )
            .into();

            let mut inside_results = Vec::new();
            let mut requirement_facts = Vec::new();
            let mut requirement_roles = Vec::new();
            if verify_requirements {
                for (requirement, role) in [
                    (
                        first_is_set,
                        BuiltinTheoremRequirementRole::FirstArgumentIsSet,
                    ),
                    (
                        second_is_finite,
                        BuiltinTheoremRequirementRole::SecondArgumentIsFiniteSet,
                    ),
                    (
                        subset,
                        BuiltinTheoremRequirementRole::FirstArgumentSubsetOfSecond,
                    ),
                ] {
                    self.verify_atomic_fact_well_defined(&requirement, &verify_state)?;
                    let result = self.verify_atomic_fact(&requirement, &verify_state)?;
                    if !result.is_success() {
                        return Err(builtin_thm_exec_error(
                            stmt,
                            format!(
                                "builtin theorem `subset_of_finite_set_is_finite` requires that {}",
                                role.as_str()
                            ),
                            vec![result],
                        ));
                    }
                    requirement_facts.push(requirement.into());
                    requirement_roles.push(role);
                    inside_results.push(result);
                }
                self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
            }

            let store_reason = InferReason::Other(format!("builtin theorem `{}`", name));
            let infer_result = if verify_requirements {
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    conclusion.clone(),
                    store_reason.store_reason(),
                )?
            } else {
                self.store_trusted_fact_and_infer_with_reason(
                    conclusion.clone().into(),
                    store_reason,
                )?
            };
            let verification = SuccessVerifyTheoremApplicationResult::new_builtin(
                theorem_id,
                stmt.args.clone(),
                requirement_facts,
                requirement_roles,
                vec![conclusion.clone().into()],
                inside_results,
                None,
            );
            return Ok(Some(
                SuccessStmtResult::ReleaseThmStmt(Box::new(SuccessReleaseThmStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(verification),
                }))
                .into(),
            ));
        }

        if name == "finite_set_has_bijective_index" {
            require_arity!(1);

            let finite_set = stmt.args[0].clone();
            let size: Obj = FiniteSetSize::new(finite_set.clone()).into();
            let sequence_set: Obj = FiniteSeqSet::new(finite_set.clone(), size.clone()).into();
            let index_group = self.fresh_param_group_with_type(
                vec!["idx".to_string()],
                ParamType::Obj(sequence_set),
            )?;
            let index = obj_for_bound_param_in_scope(&index_group.params[0]);
            let domain: Obj = ClosedRange::new(Number::new("1".to_string()).into(), size).into();
            let bijective: AtomicFact = NormalAtomicFact::new(
                AtomicName::WithoutMod(BIJECTIVE.to_string()),
                vec![domain, finite_set.clone(), index],
                stmt.line_file.clone(),
            )
            .into();
            let body = ExistentialSpec::new(
                TypedParameterList::new(vec![index_group]),
                vec![bijective.into()],
                stmt.line_file.clone(),
            )?;
            let conclusion: ExistOrAndChainAtomicFact = ExistFactEnum::ExistFact(body).into();

            let mut inside_results = Vec::new();
            let mut requirement_facts = Vec::new();
            let mut requirement_roles = Vec::new();
            if verify_requirements {
                let finite_requirement: AtomicFact =
                    IsFiniteSetFact::new(finite_set, stmt.line_file.clone()).into();
                self.verify_atomic_fact_well_defined(&finite_requirement, &verify_state)?;
                let result = self.verify_atomic_fact(&finite_requirement, &verify_state)?;
                if !result.is_success() {
                    return Err(builtin_thm_exec_error(
                        stmt,
                        "builtin theorem `finite_set_has_bijective_index` requires a finite-set argument"
                            .to_string(),
                        vec![result],
                    ));
                }
                requirement_facts.push(finite_requirement.into());
                requirement_roles.push(BuiltinTheoremRequirementRole::ArgumentIsFiniteSet);
                inside_results.push(result);
                self.verify_exist_or_and_chain_atomic_fact_well_defined(
                    &conclusion,
                    &verify_state,
                )?;
            }

            let store_reason = InferReason::Other(format!("builtin theorem `{}`", name));
            let infer_result = if verify_requirements {
                self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    conclusion.clone(),
                    store_reason.store_reason(),
                )?
            } else {
                self.store_trusted_fact_and_infer_with_reason(
                    conclusion.clone().to_fact(),
                    store_reason,
                )?
            };
            let verification = SuccessVerifyTheoremApplicationResult::new_builtin(
                theorem_id,
                stmt.args.clone(),
                requirement_facts,
                requirement_roles,
                vec![conclusion.clone().to_fact()],
                inside_results,
                None,
            );
            return Ok(Some(
                SuccessStmtResult::ReleaseThmStmt(Box::new(SuccessReleaseThmStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(verification),
                }))
                .into(),
            ));
        }

        if name == "rational_has_unique_reduced_fraction" {
            require_arity!(1);

            let numerator_group = self.fresh_param_group_with_type(
                vec!["p".to_string()],
                ParamType::Obj(StandardSet::Z.into()),
            )?;
            let denominator_group = self.fresh_param_group_with_type(
                vec!["d".to_string()],
                ParamType::Obj(StandardSet::NPos.into()),
            )?;
            let numerator = obj_for_bound_param_in_scope(&numerator_group.params[0]);
            let denominator = obj_for_bound_param_in_scope(&denominator_group.params[0]);
            let ratio: Obj = Div::new(numerator.clone(), denominator.clone()).into();
            let gcd: Obj = Gcd::new(numerator, denominator).into();
            let ratio_fact: AtomicFact =
                EqualFact::new(stmt.args[0].clone(), ratio, stmt.line_file.clone()).into();
            let coprime_fact: AtomicFact = EqualFact::new(
                gcd,
                Number::new("1".to_string()).into(),
                stmt.line_file.clone(),
            )
            .into();
            let body = ExistentialSpec::new(
                TypedParameterList::new(vec![numerator_group, denominator_group]),
                vec![ratio_fact.into(), coprime_fact.into()],
                stmt.line_file.clone(),
            )?;
            let conclusion: ExistOrAndChainAtomicFact = ExistFactEnum::ExistUniqueFact(body).into();

            let rational_requirement: AtomicFact = InFact::new(
                stmt.args[0].clone(),
                StandardSet::Q.into(),
                stmt.line_file.clone(),
            )
            .into();

            let verification = if verify_requirements {
                Some(self.verify_atomic_fact_restricted_known_builtin(
                    &rational_requirement,
                    &verify_state,
                )?)
            } else {
                None
            };
            let mut inside_results = Vec::new();
            let mut requirement_facts = Vec::new();
            let mut requirement_roles = Vec::new();
            if let Some(result) = verification {
                if !result.is_success() {
                    return Err(builtin_thm_exec_error(
                        stmt,
                        "builtin theorem `rational_has_unique_reduced_fraction` requires its argument to belong to `Q`"
                            .to_string(),
                        vec![result],
                    ));
                }
                requirement_facts.push(rational_requirement.into());
                requirement_roles.push(BuiltinTheoremRequirementRole::ArgumentBelongsToRationals);
                inside_results.push(result);
                self.verify_exist_or_and_chain_atomic_fact_well_defined(
                    &conclusion,
                    &verify_state,
                )?;
            }

            let store_reason = InferReason::Other(format!("builtin theorem `{}`", name));
            let infer_result = if verify_requirements {
                self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    conclusion.clone(),
                    store_reason.store_reason(),
                )?
            } else {
                self.store_trusted_fact_and_infer_with_reason(
                    conclusion.clone().to_fact(),
                    store_reason,
                )?
            };
            let verification = SuccessVerifyTheoremApplicationResult::new_builtin(
                theorem_id,
                stmt.args.clone(),
                requirement_facts,
                requirement_roles,
                vec![conclusion.clone().to_fact()],
                inside_results,
                None,
            );
            return Ok(Some(
                SuccessStmtResult::ReleaseThmStmt(Box::new(SuccessReleaseThmStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(verification),
                }))
                .into(),
            ));
        }

        let (conclusion, requirement_role, verification, provenance): (
            AtomicFact,
            BuiltinTheoremRequirementRole,
            Option<StmtResult>,
            Option<BuiltinTheoremProvenance>,
        ) = match name {
            "fn_set_member" => {
                require_arity!(2);
                let fn_set = match &stmt.args[1] {
                    Obj::FnSet(fn_set) => fn_set.clone(),
                    Obj::FiniteSeqSet(set) => {
                        self.finite_seq_set_to_fn_set(set, stmt.line_file.clone())
                    }
                    Obj::SeqSet(set) => self.seq_set_to_fn_set(set, stmt.line_file.clone()),
                    Obj::MatrixSet(set) => self.matrix_set_to_fn_set(set, stmt.line_file.clone()),
                    _ => {
                        return Err(builtin_thm_shape_error(
                            stmt,
                            name,
                            "second argument must be a `fn`, sequence, or matrix function set",
                        ));
                    }
                };
                let conclusion: AtomicFact = InFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let automatic_result = self
                        .verify_non_equational_atomic_fact_with_bounded_builtin_routes(
                            &conclusion,
                        )?;
                    if automatic_result.is_success() {
                        Some(automatic_result)
                    } else if matches!(
                        (&stmt.args[0], &stmt.args[1]),
                        (
                            Obj::MatrixAdd(_)
                                | Obj::MatrixSub(_)
                                | Obj::MatrixMul(_)
                                | Obj::MatrixScalarMul(_)
                                | Obj::MatrixPow(_),
                            Obj::MatrixSet(_)
                        )
                    ) {
                        let element = &stmt.args[0];
                        let Obj::MatrixSet(expected) = &stmt.args[1] else {
                            unreachable!("matrix target was checked above")
                        };
                        let actual = self.real_matrix_type(element, &verify_state, "operator")?;
                        let real: Obj = StandardSet::R.into();
                        let steps = vec![
                            self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                                &actual.set,
                                &expected.set,
                                stmt.line_file.clone(),
                            )),
                            self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                                &expected.set,
                                &real,
                                stmt.line_file.clone(),
                            )),
                            self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                                &actual.row_len,
                                &expected.row_len,
                                stmt.line_file.clone(),
                            )),
                            self.verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                                &actual.col_len,
                                &expected.col_len,
                                stmt.line_file.clone(),
                            )),
                        ];
                        if steps.iter().all(StmtResult::is_success) {
                            Some(
                                    SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                                        conclusion.clone().into(),
                                        "real matrix operator has the requested matrix type"
                                            .to_string(),
                                        steps,
                                    )
                                    .into(),
                                )
                        } else {
                            Some(UnknownGenericStmtResult::new().into())
                        }
                    } else {
                        let expanded_in_fact = InFact::new(
                            stmt.args[0].clone(),
                            fn_set.clone().into(),
                            stmt.line_file.clone(),
                        );
                        let mut result = match &stmt.args[0] {
                            Obj::AnonymousFn(anonymous_fn) => self
                                .verify_anonymous_fn_in_fn_set_explicit(
                                    anonymous_fn,
                                    &fn_set,
                                    &expanded_in_fact,
                                    &verify_state,
                                )?,
                            element => self.verify_in_fact_element_in_fn_set_by_stored_definition(
                                element,
                                &fn_set,
                                &expanded_in_fact,
                            )?,
                        };
                        if !result.is_success() {
                            if let Some(pointwise_result) = self
                                .verify_in_fact_element_in_fn_set_by_pointwise_values(
                                    &stmt.args[0],
                                    &fn_set,
                                    &expanded_in_fact,
                                    &verify_state,
                                )?
                            {
                                result = pointwise_result;
                            }
                        }
                        Some(result)
                    }
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::FunctionSignatureMatchesTarget,
                    verification,
                    None,
                )
            }
            "set_builder_member" => {
                require_arity!(2);
                let Obj::SetBuilder(set_builder) = &stmt.args[1] else {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "second argument must be a set builder",
                    ));
                };
                let conclusion: AtomicFact = InFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::InFact(in_fact) = &conclusion else {
                        unreachable!()
                    };
                    Some(self.verify_in_fact_in_set_builder_by_defining_facts(
                        in_fact,
                        set_builder,
                        &verify_state,
                    )?)
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::SetBuilderDefiningFacts,
                    verification,
                    None,
                )
            }
            "defined_set_member" => {
                require_arity!(2);
                let conclusion: AtomicFact = InFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::InFact(in_fact) = &conclusion else {
                        unreachable!()
                    };
                    Some(
                        self.maybe_verify_in_fact_in_unfolded_user_defined_set(
                            in_fact,
                            &verify_state,
                        )?
                        .unwrap_or_else(|| UnknownGenericStmtResult::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::DefinedSetMembership,
                    verification,
                    None,
                )
            }
            "struct_member" => {
                require_arity!(2);
                let Obj::StructObj(struct_obj) = &stmt.args[1] else {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "second argument must be a struct object",
                    ));
                };
                let conclusion: AtomicFact = InFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::InFact(in_fact) = &conclusion else {
                        unreachable!()
                    };
                    Some(self.verify_in_fact_by_struct_obj(in_fact, struct_obj, &verify_state)?)
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::StructCarrierFacts,
                    verification,
                    None,
                )
            }
            "cart_member_from_coordinates" => {
                require_arity!(2);
                let conclusion: AtomicFact = InFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let automatic = self
                        .verify_non_equational_atomic_fact_with_bounded_builtin_routes(
                            &conclusion,
                        )?;
                    if automatic.is_success() {
                        Some(automatic)
                    } else {
                        let AtomicFact::InFact(in_fact) = &conclusion else {
                            unreachable!()
                        };
                        Some(
                            self.try_verify_in_fact_by_symbolic_cart(in_fact, &verify_state)?
                                .unwrap_or_else(|| UnknownGenericStmtResult::new().into()),
                        )
                    }
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::CartesianCoordinates,
                    verification,
                    None,
                )
            }
            "general_cart_member" => {
                require_arity!(2);
                let Obj::GeneralCart(general_cart) = &stmt.args[1] else {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "second argument must be `general_cart(...)`",
                    ));
                };
                let conclusion: AtomicFact = InFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::InFact(in_fact) = &conclusion else {
                        unreachable!()
                    };
                    Some(self.verify_in_fact_in_general_cart_by_defining_facts(
                        in_fact,
                        general_cart,
                        &verify_state,
                    )?)
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::GeneralCartesianPointwiseMembership,
                    verification,
                    None,
                )
            }
            "general_cart_nonempty_by_choice_from_family"
            | "general_cart_nonempty_by_choice_from_pointwise" => {
                require_arity!(1);
                if !matches!(&stmt.args[0], Obj::GeneralCart(_)) {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "argument must be `general_cart(...)`",
                    ));
                }
                let conclusion: AtomicFact =
                    IsNonemptySetFact::new(stmt.args[0].clone(), stmt.line_file.clone()).into();
                let pointwise = name.ends_with("_from_pointwise");
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::IsNonemptySetFact(nonempty) = &conclusion else {
                        unreachable!()
                    };
                    Some(self.verify_general_cart_nonempty_by_choice_explicit(
                        nonempty,
                        pointwise,
                        &verify_state,
                    )?)
                } else {
                    None
                };
                (
                    conclusion,
                    if pointwise {
                        BuiltinTheoremRequirementRole::GeneralCartesianPointwiseNonempty
                    } else {
                        BuiltinTheoremRequirementRole::GeneralCartesianFamilyNonempty
                    },
                    verification,
                    Some(BuiltinTheoremProvenance::AxiomOfChoice),
                )
            }
            "sum_le_sum_from_pointwise" => {
                require_arity!(2);
                if !matches!((&stmt.args[0], &stmt.args[1]), (Obj::Sum(_), Obj::Sum(_))) {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "both arguments must be `sum(...)` objects",
                    ));
                }
                let conclusion: AtomicFact = LessEqualFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::LessEqualFact(fact) = &conclusion else {
                        unreachable!()
                    };
                    Some(
                        self.try_less_equal_sum_pointwise_on_same_integer_range(
                            fact,
                            &conclusion,
                            &verify_state,
                        )?
                        .unwrap_or_else(|| UnknownGenericStmtResult::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::IntegerSumPointwiseOrder,
                    verification,
                    None,
                )
            }
            "finite_set_sum_le_from_pointwise" => {
                require_arity!(2);
                if !matches!(
                    (&stmt.args[0], &stmt.args[1]),
                    (Obj::SumOfFiniteSet(_), Obj::SumOfFiniteSet(_))
                ) {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "both arguments must be `finite_set_sum(...)` objects",
                    ));
                }
                let conclusion: AtomicFact = LessEqualFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::LessEqualFact(fact) = &conclusion else {
                        unreachable!()
                    };
                    Some(
                        self.try_less_equal_finite_set_sum_pointwise_on_same_set(
                            fact,
                            &conclusion,
                            &verify_state,
                        )?
                        .unwrap_or_else(|| UnknownGenericStmtResult::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::FiniteSetSumPointwiseOrder,
                    verification,
                    None,
                )
            }
            "finite_set_summand_le_sum" => {
                require_arity!(2);
                if !matches!(&stmt.args[1], Obj::SumOfFiniteSet(_)) {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "second argument must be `finite_set_sum(...)`",
                    ));
                }
                let conclusion: AtomicFact = LessEqualFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let AtomicFact::LessEqualFact(fact) = &conclusion else {
                        unreachable!()
                    };
                    Some(
                        self.try_less_equal_finite_set_summand_nonnegative_sum(
                            fact,
                            &conclusion,
                            &verify_state,
                        )?
                        .unwrap_or_else(|| UnknownGenericStmtResult::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::FiniteSetSummandNonnegative,
                    verification,
                    None,
                )
            }
            "tuple_equal_from_coordinates" => {
                require_arity!(2);
                let conclusion: AtomicFact = EqualFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let literal = self.try_verify_tuple_equality_from_dim_and_projections(
                        &EqualFact::new_from_refs(
                            &stmt.args[0],
                            &stmt.args[1],
                            stmt.line_file.clone(),
                        ),
                        &verify_state,
                    )?;
                    Some(if let Some(result) = literal {
                        result
                    } else {
                        self.try_verify_symbolic_tuple_equality_from_coordinates(
                            &EqualFact::new_from_refs(
                                &stmt.args[0],
                                &stmt.args[1],
                                stmt.line_file.clone(),
                            ),
                            &verify_state,
                        )?
                        .unwrap_or_else(|| UnknownGenericStmtResult::new().into())
                    })
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::TupleCoordinatesEqual,
                    verification,
                    None,
                )
            }
            "finite_set_sum_substitution" => {
                require_arity!(2);
                if !matches!(
                    (&stmt.args[0], &stmt.args[1]),
                    (Obj::SumOfFiniteSet(_), Obj::SumOfFiniteSet(_))
                ) {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "both arguments must be `finite_set_sum(...)` objects",
                    ));
                }
                let conclusion: AtomicFact = EqualFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let builtin_state = BuiltinRuleSearchState::initial();
                    let pointwise = self.try_verify_finite_set_sum_pointwise_equality(
                        &EqualFact::new_from_refs(
                            &stmt.args[0],
                            &stmt.args[1],
                            stmt.line_file.clone(),
                        ),
                        &builtin_state,
                    )?;
                    Some(if let Some(result) = pointwise {
                        result
                    } else {
                        self.try_verify_finite_set_sum_substitution(
                            &EqualFact::new_from_refs(
                                &stmt.args[0],
                                &stmt.args[1],
                                stmt.line_file.clone(),
                            ),
                            &builtin_state,
                        )?
                        .unwrap_or_else(|| UnknownGenericStmtResult::new().into())
                    })
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::FiniteSetSumSubstitution,
                    verification,
                    None,
                )
            }
            "sum_over_bijective_finite_set_enumerations" => {
                require_arity!(2);
                if !matches!((&stmt.args[0], &stmt.args[1]), (Obj::Sum(_), Obj::Sum(_))) {
                    return Err(builtin_thm_shape_error(
                        stmt,
                        name,
                        "both arguments must be `sum(...)` objects",
                    ));
                }
                let conclusion: AtomicFact = EqualFact::new(
                    stmt.args[0].clone(),
                    stmt.args[1].clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let verification = if verify_requirements {
                    self.verify_atomic_fact_well_defined(&conclusion, &verify_state)?;
                    let builtin_state = BuiltinRuleSearchState::initial();
                    Some(
                        self.try_verify_sum_over_bijective_finite_set_enumerations(
                            &EqualFact::new_from_refs(
                                &stmt.args[0],
                                &stmt.args[1],
                                stmt.line_file.clone(),
                            ),
                            &builtin_state,
                        )?
                        .unwrap_or_else(|| UnknownGenericStmtResult::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    BuiltinTheoremRequirementRole::BijectiveFiniteSetEnumerations,
                    verification,
                    None,
                )
            }
            _ => unreachable!("reserved builtin theorem name is covered by the central match"),
        };

        let mut inside_results = Vec::new();
        let mut requirement_facts = Vec::new();
        let mut requirement_roles = Vec::new();
        if let Some(mut result) = verification {
            if !result.is_success() {
                return Err(builtin_thm_exec_error(
                    stmt,
                    format!(
                        "builtin theorem `{}` requirement is not verified: {}",
                        name,
                        requirement_role.as_str()
                    ),
                    vec![result],
                ));
            }
            let conclusion_well_definedness =
                self.verify_fact_well_defined_result(&conclusion.clone().into(), &verify_state)?;
            let StmtResult::Success(SuccessStmtResult::Fact(requirement_result)) = &mut result
            else {
                return Err(builtin_thm_exec_error(
                    stmt,
                    format!(
                        "builtin theorem `{}` retained a non-factual requirement Result",
                        name
                    ),
                    vec![result],
                ));
            };
            requirement_result.well_definedness = conclusion_well_definedness;
            let verified_requirement = result
                .factual_success()
                .map(|success| success.fact())
                .unwrap_or_else(|| conclusion.clone().into());
            requirement_facts.push(verified_requirement);
            requirement_roles.push(requirement_role.clone());
            inside_results.push(result);
        }

        let store_reason = InferReason::Other(format!("builtin theorem `{}`", name));
        let infer_result = if verify_requirements {
            self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                conclusion.clone(),
                store_reason.store_reason(),
            )?
        } else {
            self.store_trusted_fact_and_infer_with_reason(conclusion.clone().into(), store_reason)?
        };
        let verification = SuccessVerifyTheoremApplicationResult::new_builtin(
            theorem_id,
            stmt.args.clone(),
            requirement_facts,
            requirement_roles,
            vec![conclusion.clone().into()],
            inside_results,
            provenance,
        );
        Ok(Some(
            SuccessStmtResult::ReleaseThmStmt(Box::new(SuccessReleaseThmStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(verification),
            }))
            .into(),
        ))
    }
}

fn builtin_thm_exec_error(
    stmt: &ReleaseThmStmt,
    message: String,
    inside_results: Vec<StmtResult>,
) -> RuntimeError {
    short_exec_error(stmt.clone().into(), message, None, inside_results)
}

fn builtin_thm_shape_error(stmt: &ReleaseThmStmt, name: &str, expected: &str) -> RuntimeError {
    builtin_thm_exec_error(
        stmt,
        format!(
            "builtin theorem `{}` has invalid target shape: {}",
            name, expected
        ),
        vec![],
    )
}

/// The completeness certificate is deliberately tied to one transparent,
/// epsilon-based source interface. This fail-closed check prevents a source
/// file from redefining “Cauchy” or “convergent” to obtain an unrelated fact.
fn validate_real_sequence_completeness_definition_contract(
    runtime: &Runtime,
    stmt: &ReleaseThmStmt,
) -> Result<(), RuntimeError> {
    let contracts = [
        (
            "is_sequence_tail_close_to_limit",
            format!(
                "prop is_sequence_tail_close_to_limit(a seq(R), L R, epsilon R+, n0 N+):\n    forall n N+:\n        n >= n0\n        =>:\n            abs (a(n) - L) < epsilon"
            ),
        ),
        (
            "converges_to",
            "prop converges_to(a seq(R), L R):\n    forall epsilon R+:\n        exist n0 N+ st {$is_sequence_tail_close_to_limit(a, L, epsilon, n0)}".to_string(),
        ),
        (
            "is_convergent_sequence",
            "prop is_convergent_sequence(a seq(R)):\n    exist L R st {$converges_to(a, L)}".to_string(),
        ),
        (
            "is_cauchy_tail",
            format!(
                "prop is_cauchy_tail(a seq(R), epsilon R+, n0 N+):\n    forall m, n N+:\n        m >= n0\n        n >= n0\n        =>:\n            abs (a(m) - a(n)) < epsilon"
            ),
        ),
        (
            "is_cauchy_sequence",
            "prop is_cauchy_sequence(a seq(R)):\n    forall epsilon R+:\n        exist n0 N+ st {$is_cauchy_tail(a, epsilon, n0)}".to_string(),
        ),
    ];
    for (name, expected) in contracts {
        let Some(definition) = runtime.get_active_prop_definition_by_name(name) else {
            return Err(builtin_thm_exec_error(
                stmt,
                format!(
                    "builtin theorem `real_cauchy_sequence_converges` requires the concrete `{name}` definition"
                ),
                vec![],
            ));
        };
        if without_bound_symbol_display_ids(&definition.to_string()) != expected {
            return Err(builtin_thm_exec_error(
                stmt,
                format!(
                    "builtin theorem `real_cauchy_sequence_converges` rejected `{name}` because it does not match the checked epsilon-definition contract"
                ),
                vec![],
            ));
        }
    }
    Ok(())
}
