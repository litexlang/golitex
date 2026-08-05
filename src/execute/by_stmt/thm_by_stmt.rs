use crate::prelude::*;

impl Runtime {
    pub fn exec_by_thm_stmt(&mut self, stmt: &ByThmStmt) -> Result<StmtResult, RuntimeError> {
        if stmt.selected_fact.is_some() {
            return self.exec_by_thm_stmt_select_atomic_fact(stmt);
        }
        if let Some(result) = self.exec_builtin_thm_stmt(stmt)? {
            return Ok(result);
        }
        let thm_name = stmt.name.to_string();
        let thm = self.get_thm_definition_by_name(&thm_name).ok_or_else(|| {
            short_exec_error(
                stmt.clone().into(),
                format!("by thm: theorem `{}` is not defined", stmt.name),
                None,
                vec![],
            )
        })?;

        let verify_state = UseContextVerifyState::new(0, false);
        let arg_type_result = self
            .verify_args_satisfy_param_def_flat_types(
                &thm.forall_fact.params_def_with_type,
                &stmt.args,
                &verify_state,
                ParamObjType::Forall,
            )
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: arguments do not match theorem parameters",
                        stmt.name
                    ),
                    Some(e),
                    vec![],
                )
            })?;
        if arg_type_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by thm `{}`: could not verify argument parameter types",
                    stmt.name
                ),
                None,
                vec![arg_type_result],
            ));
        }

        let param_to_arg_map = thm
            .forall_fact
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(&stmt.args);

        let mut infer_result = InferResult::new();
        Self::merge_stmt_result_infers(&mut infer_result, &arg_type_result);
        let mut inside_results = vec![arg_type_result];
        let mut domain_facts = Vec::new();
        for dom_fact in thm.forall_fact.dom_facts.iter() {
            let instantiated_dom = self
                .inst_fact(
                    dom_fact,
                    &param_to_arg_map,
                    ParamObjType::TheoremInstantiation,
                    Some(stmt.line_file.clone()),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to instantiate domain fact `{}`",
                            stmt.name, dom_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            let dom_result = self
                .verify_fact_full(&instantiated_dom, &verify_state)
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to verify domain fact `{}`",
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
                        "by thm `{}`: domain fact `{}` is not verified",
                        stmt.name, instantiated_dom
                    ),
                    None,
                    vec![dom_result],
                ));
            }
            Self::merge_stmt_result_infers(&mut infer_result, &dom_result);
            domain_facts.push(instantiated_dom.to_string());
            inside_results.push(dom_result);
        }

        let mut stored_then_facts = Vec::new();
        for then_fact in thm.forall_fact.then_facts.iter() {
            let instantiated_then = self
                .inst_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &param_to_arg_map,
                    ParamObjType::TheoremInstantiation,
                    Some(&stmt.line_file),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to instantiate then fact `{}`",
                            stmt.name, then_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            stored_then_facts.push(instantiated_then.to_string());
            infer_result.new_infer_result_inside(
                self.verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer_with_reason(
                    &instantiated_then,
                    &verify_state,
                    InferReason::TheoremInstantiation,
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to store instantiated then fact `{}`",
                            stmt.name, instantiated_then
                        ),
                        Some(e),
                        vec![],
                    )
                })?,
            );
        }

        let by_verification = ByTheoremVerificationResult::new(
            thm_name,
            stmt.args.iter().map(|arg| arg.to_string()).collect(),
            domain_facts,
            stored_then_facts,
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            by_verification.into(),
        )
        .into())
    }

    pub(crate) fn exec_by_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        if stmt.selected_fact.is_some() {
            return self.exec_by_thm_stmt_select_atomic_fact_affect_environment_only(stmt);
        }
        if let Some(result) = self.exec_builtin_thm_stmt_affect_environment_only(stmt)? {
            return Ok(result);
        }
        let thm_name = stmt.name.to_string();
        let thm = self.get_thm_definition_by_name(&thm_name).ok_or_else(|| {
            short_exec_error(
                stmt.clone().into(),
                format!("by thm: theorem `{}` is not defined", stmt.name),
                None,
                vec![],
            )
        })?;

        let param_to_arg_map = thm
            .forall_fact
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(&stmt.args);

        let mut infer_result = InferResult::new();
        let mut stored_then_facts = Vec::new();
        for then_fact in thm.forall_fact.then_facts.iter() {
            let instantiated_then = self
                .inst_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &param_to_arg_map,
                    ParamObjType::TheoremInstantiation,
                    Some(&stmt.line_file),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to instantiate then fact `{}`",
                            stmt.name, then_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            stored_then_facts.push(instantiated_then.to_string());
            infer_result.new_infer_result_inside(
                self.store_trusted_fact_and_infer_with_reason(
                    instantiated_then.clone().to_fact(),
                    InferReason::TheoremInstantiation,
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to store instantiated then fact `{}`",
                            stmt.name, instantiated_then
                        ),
                        Some(e),
                        vec![],
                    )
                })?,
            );
        }

        let by_verification = ByTheoremVerificationResult::new(
            thm_name,
            stmt.args.iter().map(|arg| arg.to_string()).collect(),
            vec![],
            stored_then_facts,
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            vec![],
            by_verification.into(),
        )
        .into())
    }

    fn exec_by_thm_stmt_select_atomic_fact(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let selected_fact = stmt
            .selected_fact
            .as_ref()
            .expect("selected by thm execution requires a target")
            .clone();
        let verify_state = UseContextVerifyState::new(0, false);
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

        let expanded_stmt = ByThmStmt::new(
            stmt.name.clone(),
            stmt.args.clone(),
            None,
            stmt.line_file.clone(),
        );
        let (mut expanded_success, target_result) = self.run_in_local_env(|rt| {
            let expanded_result = rt.exec_by_thm_stmt(&expanded_stmt).map_err(|error| {
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
            let target_result = rt
                .verify_atomic_fact(
                    &selected_fact,
                    &verify_state.with_well_defined_already_verified(),
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
            let expanded_success = expanded_result
                .into_non_factual_success()
                .expect("by thm application must return a non-factual success");
            Ok((expanded_success, target_result))
        })?;

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

        let Some(ByVerificationResult::Theorem(mut verification)) =
            expanded_success.by_verification.take()
        else {
            unreachable!("by thm application must contain theorem verification metadata")
        };
        verification.select_atomic_fact(selected_fact.to_string());
        let mut inside_results = expanded_success.inside_results;
        inside_results.push(target_result);
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            verification.into(),
        )
        .into())
    }

    fn exec_by_thm_stmt_select_atomic_fact_affect_environment_only(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let selected_fact = stmt
            .selected_fact
            .as_ref()
            .expect("selected by thm execution requires a target")
            .clone();
        let expanded_stmt = ByThmStmt::new(
            stmt.name.clone(),
            stmt.args.clone(),
            None,
            stmt.line_file.clone(),
        );
        let mut expanded_success = self.run_in_local_env(|rt| {
            rt.exec_by_thm_stmt_affect_environment_only(&expanded_stmt)
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
                })?
                .into_non_factual_success()
                .ok_or_else(|| {
                    short_exec_error(
                        stmt.clone().into(),
                        "by thm: theorem application returned an invalid result".to_string(),
                        None,
                        vec![],
                    )
                })
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

        let Some(ByVerificationResult::Theorem(mut verification)) =
            expanded_success.by_verification.take()
        else {
            unreachable!("by thm application must contain theorem verification metadata")
        };
        verification.select_atomic_fact(selected_fact.to_string());
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            expanded_success.inside_results,
            verification.into(),
        )
        .into())
    }

    fn merge_stmt_result_infers(infer_result: &mut InferResult, stmt_result: &StmtResult) {
        infer_result.new_infer_result_inside(stmt_result.infer_result());
    }

    fn exec_builtin_thm_stmt(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        self.exec_builtin_thm_stmt_impl(stmt, true)
    }

    fn exec_builtin_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &ByThmStmt,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        self.exec_builtin_thm_stmt_impl(stmt, false)
    }

    fn exec_builtin_thm_stmt_impl(
        &mut self,
        stmt: &ByThmStmt,
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

        let verify_state = UseContextVerifyState::new(0, false);
        let (conclusion, requirement_role, verification, provenance): (
            AtomicFact,
            String,
            Option<StmtResult>,
            Option<String>,
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
                        .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                            &conclusion,
                        )?;
                    if automatic_result.is_true() {
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
                            self.verify_objs_are_equal_by_known_equality(
                                &actual.set,
                                &expected.set,
                                stmt.line_file.clone(),
                            ),
                            self.verify_objs_are_equal_by_known_equality(
                                &expected.set,
                                &real,
                                stmt.line_file.clone(),
                            ),
                            self.verify_objs_are_equal_by_known_equality(
                                &actual.row_len,
                                &expected.row_len,
                                stmt.line_file.clone(),
                            ),
                            self.verify_objs_are_equal_by_known_equality(
                                &actual.col_len,
                                &expected.col_len,
                                stmt.line_file.clone(),
                            ),
                        ];
                        if steps.iter().all(StmtResult::is_true) {
                            Some(
                                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                        conclusion.clone().into(),
                                        "real matrix operator has the requested matrix type"
                                            .to_string(),
                                        steps,
                                    )
                                    .into(),
                                )
                        } else {
                            Some(StmtUnknown::new().into())
                        }
                    } else {
                        let expanded_in_fact = InFact::new(
                            stmt.args[0].clone(),
                            fn_set.clone().into(),
                            stmt.line_file.clone(),
                        );
                        let mut result = match &stmt.args[0] {
                            Obj::AnonymousFn(anonymous_fn) => self
                                .verify_in_fact_anonymous_fn_signature_matches_fn_set(
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
                        if !result.is_true() {
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
                    "function signature matches the target function set".to_string(),
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
                    "element satisfies the set-builder base and defining facts".to_string(),
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
                        .unwrap_or_else(|| StmtUnknown::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    "one set-valued definition unfolds and its membership obligations hold"
                        .to_string(),
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
                    "element satisfies the struct carrier and equivalent facts".to_string(),
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
                        .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                            &conclusion,
                        )?;
                    if automatic.is_true() {
                        Some(automatic)
                    } else {
                        let AtomicFact::InFact(in_fact) = &conclusion else {
                            unreachable!()
                        };
                        Some(
                            self.try_verify_in_fact_by_symbolic_cart(in_fact, &verify_state)?
                                .unwrap_or_else(|| StmtUnknown::new().into()),
                        )
                    }
                } else {
                    None
                };
                (
                    conclusion,
                    "tuple/cart dimensions and coordinate memberships hold".to_string(),
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
                    "function carrier and pointwise general-cart membership hold".to_string(),
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
                        "every indexed factor is nonempty"
                    } else {
                        "every member of the family set is nonempty"
                    }
                    .to_string(),
                    verification,
                    Some("axiom_of_choice".to_string()),
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
                        .unwrap_or_else(|| StmtUnknown::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    "summation bounds agree and summands are pointwise ordered".to_string(),
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
                        .unwrap_or_else(|| StmtUnknown::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    "finite index sets agree and summands are pointwise ordered".to_string(),
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
                        .unwrap_or_else(|| StmtUnknown::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    "term belongs to the index set and every summand is nonnegative".to_string(),
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
                        &stmt.args[0],
                        &stmt.args[1],
                        stmt.line_file.clone(),
                        &verify_state,
                    )?;
                    Some(if let Some(result) = literal {
                        result
                    } else {
                        self.try_verify_symbolic_tuple_equality_from_coordinates(
                            &stmt.args[0],
                            &stmt.args[1],
                            stmt.line_file.clone(),
                            &verify_state,
                        )?
                        .unwrap_or_else(|| StmtUnknown::new().into())
                    })
                } else {
                    None
                };
                (
                    conclusion,
                    "tuple dimensions and all corresponding coordinates agree".to_string(),
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
                    let builtin_state = UseBuiltinRuleVerifyState::new();
                    let pointwise = self.try_verify_finite_set_sum_pointwise_equality(
                        &stmt.args[0],
                        &stmt.args[1],
                        stmt.line_file.clone(),
                        &builtin_state,
                    )?;
                    Some(if let Some(result) = pointwise {
                        result
                    } else {
                        self.try_verify_finite_set_sum_substitution(
                            &stmt.args[0],
                            &stmt.args[1],
                            stmt.line_file.clone(),
                            &builtin_state,
                        )?
                        .unwrap_or_else(|| StmtUnknown::new().into())
                    })
                } else {
                    None
                };
                (
                    conclusion,
                    "summands agree pointwise on one index set, or by pullback along a bijection"
                        .to_string(),
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
                    let builtin_state = UseBuiltinRuleVerifyState::new();
                    Some(
                        self.try_verify_sum_over_bijective_finite_set_enumerations(
                            &stmt.args[0],
                            &stmt.args[1],
                            stmt.line_file.clone(),
                            &builtin_state,
                        )?
                        .unwrap_or_else(|| StmtUnknown::new().into()),
                    )
                } else {
                    None
                };
                (
                    conclusion,
                    "both summations enumerate the same finite set bijectively".to_string(),
                    verification,
                    None,
                )
            }
            _ => unreachable!("reserved builtin theorem name is covered by the central match"),
        };

        let mut inside_results = Vec::new();
        let mut requirement_facts = Vec::new();
        let mut requirement_roles = Vec::new();
        if let Some(result) = verification {
            if !result.is_true() {
                return Err(builtin_thm_exec_error(
                    stmt,
                    format!(
                        "builtin theorem `{}` requirement is not verified: {}",
                        name, requirement_role
                    ),
                    vec![result],
                ));
            }
            let verified_requirement = result
                .factual_success()
                .map(|success| success.stmt.to_string())
                .unwrap_or_else(|| conclusion.to_string());
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
        let stored_then_facts = vec![conclusion.to_string()];
        let verification = ByTheoremVerificationResult::new_builtin(
            name.to_string(),
            stmt.args.iter().map(ToString::to_string).collect(),
            requirement_facts,
            requirement_roles,
            stored_then_facts,
            provenance,
        );
        Ok(Some(
            NonFactualStmtSuccess::new_with_by_verification(
                stmt.clone().into(),
                infer_result,
                inside_results,
                verification.into(),
            )
            .into(),
        ))
    }
}

fn builtin_thm_exec_error(
    stmt: &ByThmStmt,
    message: String,
    inside_results: Vec<StmtResult>,
) -> RuntimeError {
    short_exec_error(stmt.clone().into(), message, None, inside_results)
}

fn builtin_thm_shape_error(stmt: &ByThmStmt, name: &str, expected: &str) -> RuntimeError {
    builtin_thm_exec_error(
        stmt,
        format!(
            "builtin theorem `{}` has invalid target shape: {}",
            name, expected
        ),
        vec![],
    )
}
