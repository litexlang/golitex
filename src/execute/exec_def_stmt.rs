use crate::prelude::*;
use std::collections::HashMap;

fn param_defs_with_type_from_have_fn_clause(clause: &FnSetClause) -> Vec<ParamGroupWithParamType> {
    let mut param_defs_with_type: Vec<ParamGroupWithParamType> =
        Vec::with_capacity(clause.params_def_with_set.len());
    for param_def_with_set in clause.params_def_with_set.iter() {
        param_defs_with_type.push(ParamGroupWithParamType::new(
            param_def_with_set.params.clone(),
            ParamType::Obj(param_def_with_set.set.clone()),
        ));
    }
    param_defs_with_type
}

impl Runtime {
    fn build_function_obj_with_param_names(
        &self,
        function_name: &str,
        param_names: &[String],
    ) -> Obj {
        let mut function_args: Vec<Box<Obj>> = Vec::with_capacity(param_names.len());
        for param_name in param_names.iter() {
            function_args.push(Box::new(param_name.clone().into()));
        }

        let fn_head_atom = Atom::from(Identifier::new(function_name.to_string()));
        let fn_body_groups = vec![function_args];
        FnObj::new(fn_head_atom, fn_body_groups).into()
    }

    pub fn exec_def_prop_stmt(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        self.run_in_local_env(|rt| rt.def_prop_stmt_check_well_defined(def_prop_stmt))
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    def_prop_stmt.clone().into(),
                    "".to_string(),
                    Some(e.into()),
                    vec![],
                )
            })?;
        self.store_def_prop(def_prop_stmt)?;
        Ok((NonFactualStmtSuccess::new(
                def_prop_stmt.clone().into(),
                InferResult::new(),
                vec![],
            )).into())
    }

    fn def_prop_stmt_check_well_defined(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<(), RuntimeErrorStruct> {
        self.define_params_with_type(&def_prop_stmt.params_def_with_type, false)
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    def_prop_stmt.clone().into(),
                    "".to_string(),
                    Some(e.into()),
                    vec![],
                )
            })?;

        for fact in def_prop_stmt.iff_facts.iter() {
            self.verify_fact_well_defined_and_store_and_infer(
                fact.clone(),
                &VerifyState::new(0, false),
            )
            .map_err(|inner_exec_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    def_prop_stmt.clone().into(),
                    "".to_string(),
                    Some(RuntimeError::from(inner_exec_error)),
                    vec![],
                )
            })?;
        }
        Ok(())
    }

    pub fn exec_def_abstract_prop_stmt(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        self.store_def_abstract_prop(def_abstract_prop_stmt)
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    def_abstract_prop_stmt.clone().into(),
                    "".to_string(),
                    Some(e.into()),
                    vec![],
                )
            })?;
        Ok((NonFactualStmtSuccess::new(
                def_abstract_prop_stmt.clone().into(),
                InferResult::new(),
                vec![],
            )).into())
    }

    pub fn exec_let_stmt(
        &mut self,
        def_let_stmt: &DefLetStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        let mut infer_result = self
            .define_params_with_type(&def_let_stmt.param_def, false)
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    def_let_stmt.clone().into(),
                    "".to_string(),
                    Some(e.into()),
                    vec![],
                )
            })?;
        for fact in def_let_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer(
                    fact.clone(),
                    &VerifyState::new(0, false),
                )
                .map_err(|inner_exec_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        def_let_stmt.clone().into(),
                        "".to_string(),
                        Some(RuntimeError::from(inner_exec_error)),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
            // Body facts are not added by infer() for chain/and/or/exist; record them for JSON / CLI.
            infer_result.new_fact(fact);
        }
        Ok((NonFactualStmtSuccess::new(
                def_let_stmt.clone().into(),
                infer_result,
                vec![],
            )).into())
    }

    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        let infer_result = self
            .define_params_with_type(&stmt.param_def, true)
            .map_err(|define_params_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    stmt.clone().into(),
                    "".to_string(),
                    Some(define_params_error),
                    vec![],
                )
            })?;
        Ok((NonFactualStmtSuccess::new(
                stmt.clone().into(),
                infer_result,
                vec![],
            )).into())
    }

    pub fn define_params_with_set(
        &mut self,
        param_def: &ParamGroupWithSet,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&param_def.set, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                let param_names_text = param_def.params.join(", ");
                let error_line_file = well_defined_error.line_file().clone();
                RuntimeError::new_define_params_error_with_msg_previous_error_position(
                    format!(
                        "define params with set: failed to verify set well-defined for params [{}] with set {}",
                        param_names_text, param_def.set
                    ),
                    Some(well_defined_error.into()),
                    error_line_file,
                )
            })?;
        let mut infer_result = InferResult::new();
        let facts = param_def.facts();
        for (name, fact) in param_def.params.iter().zip(facts.iter()) {
            self.store_identifier_obj(name).map_err(|runtime_error| {
                RuntimeError::new_define_params_error_with_msg_previous_error_position(
                    format!(
                        "define params with set: failed to declare parameter `{}`",
                        name
                    ),
                    Some(RuntimeError::from(runtime_error)),
                    default_line_file(),
                )
            })?;
            let fact_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(fact.clone())
                .map_err(|store_fact_error| {
                    RuntimeError::new_define_params_error_with_msg_previous_error_position(
                        format!(
                            "define params with set: failed to store in-set fact for parameter `{}`",
                            name
                        ),
                        Some(store_fact_error.into()),
                        default_line_file(),
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }

    // TODO: THIS IS A MESS
    pub fn exec_have_obj_equal_stmt(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        if ParamGroupWithParamType::number_of_params(&have_obj_equal_stmt.param_def)
            != have_obj_equal_stmt.objs_equal_to.len()
        {
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_obj_equal_stmt.clone().into(),
                "have_obj_equal_stmt: number of params in param_def does not match number of objs_equal_to".to_string(),
                None,
                vec![],
            ));
        }

        let mut current_index = 0;
        let mut param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        for param_def in have_obj_equal_stmt.param_def.iter() {
            let current_type_holder = self
                .inst_param_type(&param_def.param_type, &param_to_obj_map)
                .map_err(|runtime_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_obj_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(runtime_error),
                        vec![],
                    )
                })?;
            let current_type = &current_type_holder;
            for name in param_def.params.iter() {
                let current_param_equal_to = &have_obj_equal_stmt.objs_equal_to[current_index];

                let verify_result = self
                    .verify_obj_satisfies_param_type(
                        current_param_equal_to.clone(),
                        current_type,
                        &VerifyState::new(0, false),
                    )
                    .map_err(|verify_error| {
                        RuntimeErrorStruct::exec_stmt_new_with_stmt(
                            have_obj_equal_stmt.clone().into(),
                            "".to_string(),
                            Some(verify_error.into()),
                            vec![],
                        )
                    })?;
                if verify_result.is_unknown() {
                    let msg = format!(
                        "have_obj_equal_stmt: {} is not in type {}",
                        current_param_equal_to, current_type
                    );
                    return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        have_obj_equal_stmt.clone().into(),
                        msg,
                        None,
                        vec![],
                    ));
                }

                param_to_obj_map.insert(name.clone(), current_param_equal_to.clone());
                current_index += 1;
            }
        }

        let mut infer_result = InferResult::new();

        // define params
        let param_infer_result = self
            .define_params_with_type(&have_obj_equal_stmt.param_def, true)
            .map_err(|define_params_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_obj_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(define_params_error),
                    vec![],
                )
            })?;
        infer_result.new_infer_result_inside(param_infer_result);

        // store obj equal to
        for (name, obj) in ParamType::get_all_param_names(&have_obj_equal_stmt.param_def)
            .iter()
            .zip(have_obj_equal_stmt.objs_equal_to.iter())
        {
            let equal_to_fact = EqualFact::new(
                name.clone().into(),
                obj.clone(),
                have_obj_equal_stmt.line_file.clone(),
            ).into();
            let equal_to_fact_infer_result = self
                .store_atomic_fact_without_well_defined_verified_and_infer(equal_to_fact)
                .map_err(|store_fact_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_obj_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(store_fact_error.into()),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(equal_to_fact_infer_result);
        }

        return Ok((NonFactualStmtSuccess::new(
                have_obj_equal_stmt.clone().into(),
                infer_result,
                vec![],
            )).into());
    }

    pub fn exec_have_exist_obj_stmt(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        let exist_fact_in_have_obj_stmt = &have_exist_obj_stmt.exist_fact_in_have_obj_st;
        let verify_state = VerifyState::new(0, false);

        let result = self
            .verify_exist_fact(exist_fact_in_have_obj_stmt, &verify_state)
            .map_err(|verify_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_exist_obj_stmt.clone().into(),
                    "".to_string(),
                    Some(verify_error.into()),
                    vec![],
                )
            })?;
        if result.is_unknown() {
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_exist_obj_stmt.clone().into(),
                "have_exist_obj_stmt: exist fact is not verified".to_string(),
                None,
                vec![],
            ));
        }

        if ParamGroupWithParamType::number_of_params(
            &exist_fact_in_have_obj_stmt.params_def_with_type,
        ) != have_exist_obj_stmt.equal_tos.len()
        {
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_exist_obj_stmt.clone().into(),
                "have_exist_obj_stmt: number of params in exist does not match number of given objs".to_string(),
                None,
                vec![],
            ));
        }

        for obj in have_exist_obj_stmt.equal_tos.iter() {
            self.store_identifier_obj(obj)?;
        }

        let new_obj_names_as_identifier_objs = have_exist_obj_stmt
            .equal_tos
            .iter()
            .map(|s| s.clone().into())
            .collect();

        let mut infer_result = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers(
                &exist_fact_in_have_obj_stmt.params_def_with_type,
                &new_obj_names_as_identifier_objs,
                have_exist_obj_stmt.line_file.clone(),
            )
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_exist_obj_stmt.clone().into(),
                    "".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let param_to_obj_map = ParamGroupWithParamType::param_defs_and_args_to_param_to_arg_map(
            &exist_fact_in_have_obj_stmt.params_def_with_type,
            &new_obj_names_as_identifier_objs,
        );

        for fact in exist_fact_in_have_obj_stmt.facts.iter() {
            let instantiated_fact = self
                .inst_or_and_chain_atomic_fact(fact, &param_to_obj_map)
                .map_err(|runtime_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_exist_obj_stmt.clone().into(),
                        "".to_string(),
                        Some(runtime_error),
                        vec![],
                    )
                })?
                .to_fact();
            let fact_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(instantiated_fact)
                .map_err(|store_fact_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_exist_obj_stmt.clone().into(),
                        "".to_string(),
                        Some(store_fact_error.into()),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }

        Ok((NonFactualStmtSuccess::new(
                have_exist_obj_stmt.clone().into(),
                infer_result,
                vec![],
            )).into())
    }

    pub fn exec_have_fn_equal_stmt(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        let fn_set_stored = self
            .add_mangled_prefix_to_fn_set_clause(
                &have_fn_equal_stmt.fn_set_clause,
                have_fn_equal_stmt.line_file.clone(),
            )
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: build fn set for storage failed".to_string(),
                    Some(e.into()),
                    vec![],
                )
            })?;

        self.have_fn_equal_stmt_verify_well_defined(have_fn_equal_stmt, &fn_set_stored)
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: verify well-defined failed".to_string(),
                    Some(e.into()),
                    vec![],
                )
            })?;

        self.store_identifier_obj(&have_fn_equal_stmt.name)?;

        let function_identifier_obj =
            have_fn_equal_stmt.name.clone().into();
        let function_set_obj = Obj::FnSet(fn_set_stored.clone());
        let function_in_function_set_fact = InFact::new(
            function_identifier_obj,
            function_set_obj,
            have_fn_equal_stmt.line_file.clone(),
        ).into();
        let mut infer_result = self
            .store_fact_without_well_defined_verified_and_infer(function_in_function_set_fact)
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                )
            })?;

        let param_defs_with_type =
            param_defs_with_type_from_have_fn_clause(&have_fn_equal_stmt.fn_set_clause);
        let param_names = ParamGroupWithSet::collect_param_names(
            &have_fn_equal_stmt.fn_set_clause.params_def_with_set,
        );
        let function_obj =
            self.build_function_obj_with_param_names(&have_fn_equal_stmt.name, &param_names);

        let function_equals_equal_to_fact: AtomicFact = EqualFact::new(
            function_obj,
            have_fn_equal_stmt.equal_to.clone(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(have_fn_equal_stmt.fn_set_clause.dom_facts.len());
        for dom_fact in have_fn_equal_stmt.fn_set_clause.dom_facts.iter() {
            forall_dom_facts.push(dom_fact.clone().into());
        }
        let forall_fact = ForallFact::new(
            param_defs_with_type,
            forall_dom_facts,
            vec![function_equals_equal_to_fact.into()],
            have_fn_equal_stmt.line_file.clone(),
        );
        let forall_as_fact: Fact = forall_fact.into();
        let forall_infer_result = self
            .store_fact_without_well_defined_verified_and_infer(forall_as_fact)
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                )
            })?;

        infer_result.new_infer_result_inside(forall_infer_result);

        Ok((NonFactualStmtSuccess::new(
                have_fn_equal_stmt.clone().into(),
                infer_result,
                vec![],
            )).into())
    }

    fn have_fn_equal_stmt_verify_well_defined(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeErrorStruct> {
        self.run_in_local_env(|rt| {
            rt.have_fn_equal_stmt_verify_well_defined_body(have_fn_equal_stmt, fn_set_stored)
        })
    }

    fn have_fn_equal_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeErrorStruct> {
        let verify_state = VerifyState::new(0, false);

        // 证明 fn_set 是 well-defined 的
        let function_set_obj = Obj::FnSet(fn_set_stored.clone());
        self.verify_obj_well_defined_and_store_cache(&function_set_obj, &verify_state)
            .map_err(|well_defined_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(well_defined_error.into()),
                    vec![],
                )
            })?;

        for param_def_with_set in have_fn_equal_stmt.fn_set_clause.params_def_with_set.iter() {
            self.define_params_with_set(param_def_with_set)
                .map_err(|define_params_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_fn_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(define_params_error),
                        vec![],
                    )
                })?;
        }

        for dom_fact in have_fn_equal_stmt.fn_set_clause.dom_facts.iter() {
            let _ = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_fn_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(store_fact_error.into()),
                        vec![],
                    )
                })?;
        }

        let equal_to_in_ret_set_atomic_fact = InFact::new(
            have_fn_equal_stmt.equal_to.clone(),
            have_fn_equal_stmt.fn_set_clause.ret_set.clone(),
            have_fn_equal_stmt.line_file.clone(),
        ).into();
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(|verify_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(verify_error.into()),
                    vec![],
                )
            })?;
        if verify_result.is_unknown() {
            let msg = format!(
                "have_fn_equal_stmt: {} is not in return set {}",
                have_fn_equal_stmt.equal_to, have_fn_equal_stmt.fn_set_clause.ret_set
            );
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_fn_equal_stmt.clone().into(),
                msg,
                None,
                vec![],
            ));
        }

        Ok(())
    }

    pub fn exec_have_fn_equal_case_by_case_stmt(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        let fn_set_stored = self
            .add_mangled_prefix_to_fn_set_clause(
                &have_fn_equal_case_by_case_stmt.fn_set_clause,
                have_fn_equal_case_by_case_stmt.line_file.clone(),
            )
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "have_fn_equal_case_by_case_stmt: build fn set for storage failed".to_string(),
                    Some(e.into()),
                    vec![],
                )
            })?;

        self.verify_have_fn_equal_case_by_case_stmt(
            have_fn_equal_case_by_case_stmt,
            &fn_set_stored,
        )
        .map_err(|e| {
            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_fn_equal_case_by_case_stmt.clone().into(),
                "have_fn_equal_case_by_case_stmt: verify well-defined failed".to_string(),
                Some(e.into()),
                vec![],
            )
        })?;

        let infer_result =
            self.store_have_fn_equal_case_by_case(have_fn_equal_case_by_case_stmt, &fn_set_stored)?;
        Ok((NonFactualStmtSuccess::new(
                have_fn_equal_case_by_case_stmt.clone().into(),
                infer_result,
                vec![],
            )).into())
    }

    fn store_have_fn_equal_case_by_case(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        self.store_identifier_obj(&have_fn_equal_case_by_case_stmt.name)?;

        let function_identifier_obj = have_fn_equal_case_by_case_stmt.name.clone().into();
        let function_set_obj = Obj::FnSet(fn_set_stored.clone());
        let function_in_function_set_fact = InFact::new(
            function_identifier_obj,
            function_set_obj,
            have_fn_equal_case_by_case_stmt.line_file.clone(),
        ).into();

        let mut infer_result = self
            .store_fact_without_well_defined_verified_and_infer(function_in_function_set_fact)
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                )
            })?;

        let param_defs_with_type = param_defs_with_type_from_have_fn_clause(
            &have_fn_equal_case_by_case_stmt.fn_set_clause,
        );
        let param_names = ParamGroupWithSet::collect_param_names(
            &have_fn_equal_case_by_case_stmt
                .fn_set_clause
                .params_def_with_set,
        );
        let function_obj = self.build_function_obj_with_param_names(
            &have_fn_equal_case_by_case_stmt.name,
            &param_names,
        );

        for case_index in 0..have_fn_equal_case_by_case_stmt.cases.len() {
            let case_fact = &have_fn_equal_case_by_case_stmt.cases[case_index];
            let equal_to = &have_fn_equal_case_by_case_stmt.equal_tos[case_index];

            let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::with_capacity(
                have_fn_equal_case_by_case_stmt
                    .fn_set_clause
                    .dom_facts
                    .len()
                    + 1,
            );
            for dom_fact in have_fn_equal_case_by_case_stmt
                .fn_set_clause
                .dom_facts
                .iter()
            {
                forall_dom_facts.push(dom_fact.clone().into());
            }
            forall_dom_facts.push(case_fact.clone().into());

            let function_equals_equal_to_fact: AtomicFact = EqualFact::new(
                function_obj.clone(),
                equal_to.clone(),
                have_fn_equal_case_by_case_stmt.line_file.clone(),
            )
            .into();
            let forall_fact = ForallFact::new(
                param_defs_with_type.clone(),
                forall_dom_facts,
                vec![function_equals_equal_to_fact.into()],
                have_fn_equal_case_by_case_stmt.line_file.clone(),
            );
            let forall_as_fact: Fact = forall_fact.into();

            infer_result.new_fact(&forall_as_fact);
            let forall_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(forall_as_fact)
                .map_err(|store_fact_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "".to_string(),
                        Some(store_fact_error.into()),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(forall_infer_result);
        }

        Ok(infer_result)
    }

    pub fn exec_have_fn_by_induc_stmt(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        self.exec_have_fn_by_induc(stmt)
            .map_err(|e| e.into_struct())
    }

    fn verify_have_fn_equal_case_by_case_stmt(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeErrorStruct> {
        if have_fn_equal_case_by_case_stmt.cases.len()
            != have_fn_equal_case_by_case_stmt.equal_tos.len()
        {
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_fn_equal_case_by_case_stmt.clone().into(),
                "have_fn_equal_case_by_case_stmt: number of cases does not match number of equal_tos".to_string(),
                None,
                vec![],
            ));
        }

        // 证明 fn_set 是 well-defined 的
        let function_set_obj = Obj::FnSet(fn_set_stored.clone());
        self.verify_obj_well_defined_and_store_cache(
            &function_set_obj,
            &VerifyState::new(0, false),
        )
        .map_err(|well_defined_error| {
            RuntimeErrorStruct::exec_stmt_new_with_stmt(
                have_fn_equal_case_by_case_stmt.clone().into(),
                "".to_string(),
                Some(well_defined_error.into()),
                vec![],
            )
        })?;

        for case_index in 0..have_fn_equal_case_by_case_stmt.cases.len() {
            let case_fact = &have_fn_equal_case_by_case_stmt.cases[case_index];
            let equal_to = &have_fn_equal_case_by_case_stmt.equal_tos[case_index];

            self.run_in_local_env(|rt| {
                rt.have_fn_equal_case_by_case_stmt_verify_well_defined_body_for_one_case(
                    have_fn_equal_case_by_case_stmt,
                    case_fact,
                    equal_to,
                )
            })?;
        }

        Ok(())
    }

    fn have_fn_equal_case_by_case_stmt_verify_well_defined_body_for_one_case(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        case_fact: &AndChainAtomicFact,
        equal_to: &Obj,
    ) -> Result<(), RuntimeErrorStruct> {
        let verify_state = VerifyState::new(0, false);
        let case_fact_as_fact: Fact = case_fact.clone().into();

        for param_def_with_set in have_fn_equal_case_by_case_stmt
            .fn_set_clause
            .params_def_with_set
            .iter()
        {
            self.define_params_with_set(param_def_with_set)
                .map_err(|define_params_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "".to_string(),
                        Some(define_params_error),
                        vec![],
                    )
                })?;
        }

        for dom_fact in have_fn_equal_case_by_case_stmt
            .fn_set_clause
            .dom_facts
            .iter()
        {
            let _ = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "".to_string(),
                        Some(store_fact_error.into()),
                        vec![],
                    )
                })?;
        }

        let _ = self
            .store_fact_without_well_defined_verified_and_infer(case_fact_as_fact)
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                )
            })?;
        self.verify_obj_well_defined_and_store_cache(equal_to, &verify_state)
            .map_err(|well_defined_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "".to_string(),
                    Some(well_defined_error.into()),
                    vec![],
                )
            })?;

        let equal_to_in_ret_set_atomic_fact = InFact::new(
            equal_to.clone(),
            have_fn_equal_case_by_case_stmt
                .fn_set_clause
                .ret_set
                .clone(),
            have_fn_equal_case_by_case_stmt.line_file.clone(),
        ).into();
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(|verify_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "".to_string(),
                    Some(verify_error.into()),
                    vec![],
                )
            })?;
        if verify_result.is_unknown() {
            let msg = format!(
                "have_fn_equal_case_by_case_stmt: {} is not in return set {} under case {}",
                equal_to, have_fn_equal_case_by_case_stmt.fn_set_clause.ret_set, case_fact,
            );
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_fn_equal_case_by_case_stmt.clone().into(),
                msg,
                None,
                vec![],
            ));
        }

        Ok(())
    }
}
