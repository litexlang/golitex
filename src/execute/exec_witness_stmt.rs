use crate::prelude::*;

impl Runtime {
    pub fn exec_witness_exist_fact(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<StmtResult, RuntimeError> {
        let witness_stmt = stmt.clone().into();
        self.exec_witness_exist_fact_stmt_verify_well_definedness(stmt)?;
        let (inside_results, verification) =
            self.exec_witness_exist_fact_stmt_verify_process(stmt)?;
        let infer_result = self.exec_witness_exist_fact_stmt_affect_environment(stmt)?;

        let mut success = NonFactualStmtSuccess::new(witness_stmt, infer_result, inside_results);
        success.witness_exist_verification = Some(verification);
        Ok(success.into())
    }

    pub fn exec_witness_atomic_fact(
        &mut self,
        stmt: &WitnessAtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let witness_stmt: Stmt = stmt.clone().into();
        let (definition, instantiated_existential) = self.resolve_witness_atomic_fact(stmt)?;
        let definition_parameter_check =
            self.verify_witness_atomic_fact_definition_parameters(stmt, &definition)?;
        let expanded = WitnessExistFact::new(
            stmt.witnesses.clone(),
            instantiated_existential.clone(),
            stmt.proof.clone(),
            stmt.line_file.clone(),
        );
        self.exec_witness_exist_fact_stmt_verify_well_definedness(&expanded)
            .map_err(|cause| exec_stmt_error_with_stmt_and_cause(witness_stmt.clone(), cause))?;
        let (inside_results, witness_verification) = self
            .exec_witness_exist_fact_stmt_verify_process(&expanded)
            .map_err(|cause| exec_stmt_error_with_stmt_and_cause(witness_stmt.clone(), cause))?;
        let infer_result = self.exec_witness_atomic_fact_stmt_affect_environment(stmt)?;

        let mut success = NonFactualStmtSuccess::new(witness_stmt, infer_result, inside_results);
        success.witness_atomic_fact_verification = Some(WitnessAtomicFactVerificationResult::new(
            definition,
            instantiated_existential,
            definition_parameter_check,
            witness_verification,
        ));
        Ok(success.into())
    }

    fn resolve_witness_atomic_fact(
        &self,
        stmt: &WitnessAtomicFact,
    ) -> Result<(DefPropStmt, ExistFactEnum), RuntimeError> {
        let witness_stmt: Stmt = stmt.clone().into();
        let predicate_name = stmt.atomic_fact.predicate.to_string();
        if self
            .get_abstract_prop_definition_by_name(&predicate_name)
            .is_some()
        {
            return Err(short_exec_error(
                witness_stmt,
                format!(
                    "atomic fact witness requires a concrete `prop`; `{}` is an `abstract_prop`",
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
                    witness_stmt.clone(),
                    format!(
                        "atomic fact witness could not find a concrete prop definition for `{}`",
                        predicate_name
                    ),
                    None,
                    vec![],
                )
            })?;
        if definition.iff_facts.len() != 1 {
            return Err(short_exec_error(
                witness_stmt,
                format!(
                    "atomic fact witness requires `{}` to have exactly one definition clause whose outer form is positive `exist`",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        let Fact::ExistFact(definition_existential) = &definition.iff_facts[0] else {
            return Err(short_exec_error(
                witness_stmt,
                format!(
                    "atomic fact witness requires the sole definition clause of `{}` to be positive `exist`",
                    predicate_name
                ),
                None,
                vec![],
            ));
        };
        if definition_existential.is_exist_unique() {
            return Err(short_exec_error(
                witness_stmt,
                format!(
                    "atomic fact witness does not support the `exist!` definition of `{}`; use explicit `witness exist! ...` and then `by def`",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        if !definition_existential.is_plain_exist() {
            return Err(short_exec_error(
                witness_stmt,
                format!(
                    "atomic fact witness requires the sole definition clause of `{}` to be positive `exist`",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        let existential = self
            .instantiate_existential_prop_definition(
                &stmt.atomic_fact,
                &definition,
                &stmt.line_file,
            )
            .map_err(|cause| exec_stmt_error_with_stmt_and_cause(witness_stmt.clone(), cause))?;
        Ok((definition, existential))
    }

    fn verify_witness_atomic_fact_definition_parameters(
        &mut self,
        stmt: &WitnessAtomicFact,
        definition: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let witness_stmt: Stmt = stmt.clone().into();
            let verify_state = UseContextVerifyState::new(0, false);
            let atomic_fact: AtomicFact = stmt.atomic_fact.clone().into();
            rt.verify_atomic_fact_well_defined(&atomic_fact, &verify_state)
                .map_err(|cause| {
                    exec_stmt_error_with_stmt_and_cause(witness_stmt.clone(), cause)
                })?;
            let result = rt.verify_args_satisfy_param_def_flat_types(
                &definition.params_def_with_type,
                &stmt.atomic_fact.body,
                &verify_state,
                ParamObjType::DefHeader,
            )?;
            if result.is_unknown() {
                return Err(short_exec_error(
                    witness_stmt,
                    format!(
                        "atomic fact witness arguments do not satisfy the parameter types of `{}`",
                        definition.name
                    ),
                    None,
                    vec![result],
                ));
            }
            Ok(result)
        })
    }

    /// Mathematical contract: an existential witness supplies exactly one
    /// well-defined value per bound variable, the existential formula itself
    /// is meaningful, and every witness value satisfies its instantiated
    /// declared parameter type.
    fn exec_witness_exist_fact_stmt_verify_well_definedness(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            let witness_stmt: Stmt = stmt.clone().into();
            let verify_state_for_well_defined = UseContextVerifyState::new(0, false);

            let expected_param_count = stmt
                .exist_fact_in_witness
                .params_def_with_type()
                .number_of_params();
            if expected_param_count != stmt.equal_tos.len() {
                return Err(short_exec_error(
                    witness_stmt,
                    "witness exist fact: parameter count mismatch",
                    None,
                    vec![],
                ));
            }

            if let Err(well_defined_error) = rt.verify_exist_fact_well_defined(
                &stmt.exist_fact_in_witness,
                &verify_state_for_well_defined,
            ) {
                return Err(short_exec_error(
                    witness_stmt,
                    "witness exist fact: exist fact well-defined failed",
                    Some(well_defined_error),
                    vec![],
                ));
            }

            for equal_to_obj in stmt.equal_tos.iter() {
                if let Err(well_defined_error) = rt.verify_obj_well_defined_and_store_cache(
                    equal_to_obj,
                    &verify_state_for_well_defined,
                ) {
                    return Err(short_exec_error(
                        witness_stmt,
                        "witness exist fact: equal_to well-defined failed",
                        Some(well_defined_error),
                        vec![],
                    ));
                }
            }

            let type_check_result = rt.verify_args_satisfy_param_def_flat_types(
                stmt.exist_fact_in_witness.params_def_with_type(),
                &stmt.equal_tos,
                &verify_state_for_well_defined,
                ParamObjType::Exist,
            )?;
            if type_check_result.is_unknown() {
                return Err(short_exec_error(
                    witness_stmt,
                    "witness exist fact: witness object does not satisfy the existential parameter type"
                        .to_string(),
                    None,
                    vec![],
                ));
            }

            Ok(())
        })
    }

    fn exec_witness_exist_fact_stmt_verify_process(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<(Vec<StmtResult>, WitnessExistVerificationResult), RuntimeError> {
        self.run_in_local_env(|rt| {
            let witness_stmt: Stmt = stmt.clone().into();
            let mut inside_results: Vec<StmtResult> = Vec::new();

            // Capture concrete witness-type evidence before existential
            // parameters and their temporary equalities enter scope.  This
            // prevents the retained proof from depending on local binder
            // facts that disappear when this verification environment pops.
            let instantiated_types = rt.inst_param_def_with_type_one_by_one(
                stmt.exist_fact_in_witness.params_def_with_type(),
                &stmt.equal_tos,
                ParamObjType::Exist,
            )?;
            let flat_types = stmt
                .exist_fact_in_witness
                .params_def_with_type()
                .flat_instantiated_types_for_args(&instantiated_types);
            let mut retained_parameter_checks = Vec::with_capacity(stmt.equal_tos.len());
            for (witness, param_type) in stmt.equal_tos.iter().zip(flat_types.iter()) {
                if matches!(param_type, ParamType::Set(_)) {
                    retained_parameter_checks.push(None);
                    continue;
                }
                let result = rt.verify_obj_satisfies_param_type(
                    witness.clone(),
                    param_type,
                    &UseContextVerifyState::new(0, false),
                )?;
                if result.is_unknown() {
                    return Err(short_exec_error(
                        witness_stmt.clone(),
                        format!(
                            "witness exist fact: target-side parameter requirement for `{}` is not verified",
                            witness
                        ),
                        None,
                        vec![],
                    ));
                }
                retained_parameter_checks.push(Some(result));
            }

            rt.define_params_with_type(
                stmt.exist_fact_in_witness.params_def_with_type(),
                false,
                ParamObjType::Exist,
            )
            .map_err(|define_error| {
                short_exec_error(
                    witness_stmt.clone(),
                    "witness exist fact: failed to bind existential parameters".to_string(),
                    Some(define_error),
                    vec![],
                )
            })?;

            let exist_param_bindings = stmt
                .exist_fact_in_witness
                .params_def_with_type()
                .collect_param_bindings();
            for (binding, equal_to_obj) in exist_param_bindings.iter().zip(stmt.equal_tos.iter()) {
                let equal_fact: AtomicFact = EqualFact::new(
                    obj_for_bound_param_in_scope(binding, ParamObjType::Exist),
                    equal_to_obj.clone(),
                    stmt.line_file.clone(),
                )
                .into();
                if let Err(store_error) =
                    rt.store_atomic_fact_without_well_defined_verified_and_infer(equal_fact)
                {
                    return Err(short_exec_error(
                        witness_stmt.clone(),
                        "witness exist fact: failed to bind witness object to existential parameter"
                            .to_string(),
                        Some(store_error),
                        vec![],
                    ));
                }
            }

            for proof_stmt in stmt.proof.iter() {
                match rt.exec_stmt(proof_stmt) {
                    Ok(result) => inside_results.push(result),
                    Err(proof_exec_error) => {
                        return Err(short_exec_error(
                            witness_stmt.clone(),
                            proof_stmt.to_string(),
                            Some(proof_exec_error),
                            std::mem::take(&mut inside_results),
                        ));
                    }
                }
            }

            let proof_step_count = inside_results.len();
            let parameter_checks = retained_parameter_checks
                .into_iter()
                .map(|result| result.map(Box::new))
                .collect();

            let param_to_obj_map = stmt
                .exist_fact_in_witness
                .params_def_with_type()
                .param_defs_and_args_to_param_to_arg_map(stmt.equal_tos.as_slice());
            let instantiated_exist_fact = rt.inst_exist_fact(
                &stmt.exist_fact_in_witness,
                &param_to_obj_map,
                ParamObjType::Exist,
                None,
            )?;

            let verify_state_for_proof_check = UseContextVerifyState::new(0, false);
            let mut body_check_indices = Vec::with_capacity(instantiated_exist_fact.facts().len());
            for internal_fact_template in instantiated_exist_fact.facts().iter() {
                let internal_fact = internal_fact_template.clone().to_fact();
                let verification_result = rt
                    .verify_fact_return_err_if_not_true(
                        &internal_fact,
                        &verify_state_for_proof_check,
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            witness_stmt.clone(),
                            format!(
                                "witness exist fact: failed to verify internal fact `{}`",
                                internal_fact
                            ),
                            Some(verify_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                body_check_indices.push(inside_results.len());
                inside_results.push(verification_result);
            }

            let mut uniqueness_check_index = None;
            if stmt.exist_fact_in_witness.is_exist_unique() {
                let uniqueness_forall = rt
                    .build_exist_unique_uniqueness_forall_fact(&stmt.exist_fact_in_witness)
                    .map_err(|build_error| {
                        short_exec_error(
                            witness_stmt.clone(),
                            "witness exist!: failed to construct uniqueness obligation".to_string(),
                            Some(build_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                let uniqueness_fact: Fact = uniqueness_forall.into();
                let uniqueness_result = rt
                    .verify_fact_return_err_if_not_true(
                        &uniqueness_fact,
                        &verify_state_for_proof_check,
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            witness_stmt.clone(),
                            format!(
                                "witness exist!: failed to verify uniqueness obligation `{}`",
                                uniqueness_fact
                            ),
                            Some(verify_error),
                            std::mem::take(&mut inside_results),
                        )
                    })?;
                uniqueness_check_index = Some(inside_results.len());
                inside_results.push(uniqueness_result);
            }

            Ok((
                inside_results,
                WitnessExistVerificationResult::new(
                    proof_step_count,
                    parameter_checks,
                    body_check_indices,
                    uniqueness_check_index,
                ),
            ))
        })
    }

    pub(crate) fn exec_witness_exist_fact_stmt_affect_environment(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<InferResult, RuntimeError> {
        let witness_stmt = stmt.clone().into();
        let fact = stmt.exist_fact_in_witness.clone().into();
        let store_result = if self.current_execution_is_trusted_file() {
            self.store_trusted_fact_and_infer_with_reason(fact, InferReason::VerifiedStatement)
        } else {
            self.store_with_well_defined_verification_and_infer_with_default_verify_state(fact)
        };
        match store_result {
            Ok(infer_result) => Ok(infer_result),
            Err(store_error) => Err(short_exec_error(
                witness_stmt,
                "witness exist fact: failed to store exist fact",
                Some(store_error),
                vec![],
            )),
        }
    }

    pub(crate) fn exec_witness_exist_fact_stmt_affect_environment_only(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_witness_exist_fact_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    pub(crate) fn exec_witness_atomic_fact_stmt_affect_environment(
        &mut self,
        stmt: &WitnessAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let witness_stmt: Stmt = stmt.clone().into();
        let atomic_fact: AtomicFact = stmt.atomic_fact.clone().into();
        let fact: Fact = atomic_fact.into();
        let store_result = if self.current_execution_is_trusted_file() {
            self.store_trusted_fact_and_infer_with_reason(fact, InferReason::VerifiedStatement)
        } else {
            self.store_with_well_defined_verification_and_infer_with_default_verify_state(fact)
        };
        store_result.map_err(|store_error| {
            short_exec_error(
                witness_stmt,
                "atomic fact witness: failed to store the prop fact".to_string(),
                Some(store_error),
                vec![],
            )
        })
    }

    pub(crate) fn exec_witness_atomic_fact_stmt_affect_environment_only(
        &mut self,
        stmt: &WitnessAtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        self.resolve_witness_atomic_fact(stmt)?;
        let infer_result = self.exec_witness_atomic_fact_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    pub fn exec_witness_nonempty_set(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<StmtResult, RuntimeError> {
        let witness_stmt = stmt.clone().into();
        self.exec_witness_nonempty_set_stmt_verify_well_definedness(stmt)?;
        let inside_results = self.exec_witness_nonempty_set_stmt_verify_process(stmt)?;
        let infer_result = self.exec_witness_nonempty_set_stmt_affect_environment(stmt)?;

        Ok((NonFactualStmtSuccess::new(witness_stmt, infer_result, inside_results)).into())
    }

    /// Mathematical contract: a nonemptiness witness refers to a well-defined
    /// candidate object and a well-defined target set; the following proof
    /// phase must establish the candidate's membership.
    fn exec_witness_nonempty_set_stmt_verify_well_definedness(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            let witness_stmt: Stmt = stmt.clone().into();
            let verify_state_for_well_defined = UseContextVerifyState::new(0, false);

            if let Err(well_defined_error) = rt
                .verify_obj_well_defined_and_store_cache(&stmt.obj, &verify_state_for_well_defined)
            {
                return Err(short_exec_error(
                    witness_stmt,
                    "witness nonempty set: obj well-defined failed",
                    Some(well_defined_error),
                    vec![],
                ));
            }

            if let Err(well_defined_error) = rt
                .verify_obj_well_defined_and_store_cache(&stmt.set, &verify_state_for_well_defined)
            {
                return Err(short_exec_error(
                    witness_stmt.clone(),
                    "witness nonempty set: set well-defined failed",
                    Some(well_defined_error),
                    vec![],
                ));
            }

            Ok(())
        })
    }

    fn exec_witness_nonempty_set_stmt_verify_process(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.run_in_local_env(|rt| {
            let witness_stmt: Stmt = stmt.clone().into();
            let mut inside_results: Vec<StmtResult> = Vec::new();

            for proof_stmt in stmt.proof.iter() {
                match rt.exec_stmt(proof_stmt) {
                    Ok(result) => inside_results.push(result),
                    Err(proof_exec_error) => {
                        return Err(short_exec_error(
                            witness_stmt.clone(),
                            proof_stmt.to_string(),
                            Some(proof_exec_error),
                            std::mem::take(&mut inside_results),
                        ));
                    }
                }
            }

            if let Obj::FnSet(fn_set) = &stmt.set {
                let ret_nonempty_fact = IsNonemptySetFact::new(
                    fn_set.body.ret_set.as_ref().clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let ret_check = rt
                    .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                        &ret_nonempty_fact,
                    )?;
                if ret_check.is_true() {
                    inside_results.push(ret_check);
                    return Ok(inside_results);
                }
            }

            let membership_fact =
                InFact::new(stmt.obj.clone(), stmt.set.clone(), stmt.line_file.clone()).into();
            let verify_state_for_proof_check = UseContextVerifyState::new(0, false);
            let membership_result = rt
                .verify_fact_return_err_if_not_true(&membership_fact, &verify_state_for_proof_check)
                .map_err(|verify_error| {
                    short_exec_error(
                        witness_stmt.clone(),
                        format!(
                            "witness nonempty set: failed to verify witness membership `{}`",
                            membership_fact
                        ),
                        Some(verify_error),
                        std::mem::take(&mut inside_results),
                    )
                })?;
            inside_results.push(membership_result);

            Ok(inside_results)
        })
    }

    pub(crate) fn exec_witness_nonempty_set_stmt_affect_environment(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<InferResult, RuntimeError> {
        let witness_stmt = stmt.clone().into();
        let fact = IsNonemptySetFact::new(stmt.set.clone(), stmt.line_file.clone()).into();
        let store_result = if self.current_execution_is_trusted_file() {
            self.store_trusted_fact_and_infer_with_reason(fact, InferReason::VerifiedStatement)
        } else {
            self.store_with_well_defined_verification_and_infer_with_default_verify_state(fact)
        };
        match store_result {
            Ok(infer_result) => Ok(infer_result),
            Err(store_error) => Err(short_exec_error(
                witness_stmt,
                "witness nonempty set: failed to store nonempty set fact",
                Some(store_error),
                vec![],
            )),
        }
    }

    pub(crate) fn exec_witness_nonempty_set_stmt_affect_environment_only(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_witness_nonempty_set_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}
