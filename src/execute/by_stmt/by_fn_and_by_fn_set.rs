use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    fn build_fn_characterization_facts(
        &mut self,
        function: &Obj,
        fn_set: &FnSet,
        line_file: &LineFile,
        stmt_exec: &Stmt,
        context: &str,
    ) -> Result<(Fact, Fact, Fact, Fact), RuntimeError> {
        let param_names = ParamGroupWithSet::collect_param_names(&fn_set.params_def_with_set);
        if param_names.is_empty() {
            return Err(RuntimeError::ExecStmtError(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!("{}: fn set has no parameters", context),
                    None,
                    vec![],
                ),
            ));
        }

        let mut generated_forall_names = self
            .generate_random_unused_names(param_names.len() + 2)
            .into_iter();
        let forall_element_name = generated_forall_names.next().unwrap();
        let forall_z_name = generated_forall_names.next().unwrap();
        let generated_forall_param_names: Vec<String> = generated_forall_names.collect();
        let mut original_param_to_forall_obj: HashMap<String, Obj> =
            HashMap::with_capacity(param_names.len());
        let mut forall_param_defs_with_type: Vec<ParamGroupWithParamType> =
            Vec::with_capacity(fn_set.params_def_with_set.len());
        let mut flat_index: usize = 0;
        for param_def_with_set in fn_set.params_def_with_set.iter() {
            let next_flat_index = flat_index + param_def_with_set.params.len();
            let generated_names_for_current_group =
                generated_forall_param_names[flat_index..next_flat_index].to_vec();
            let instantiated_set = self
                .inst_obj(&param_def_with_set.set, &original_param_to_forall_obj)
                .map_err(|inst_error| {
                    RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec.clone(),
                        format!("{}: failed to instantiate generated parameter set", context),
                        Some(inst_error.into()),
                        vec![],
                    ))
                })?;
            forall_param_defs_with_type.push(ParamGroupWithParamType::new(
                generated_names_for_current_group.clone(),
                ParamType::Obj(instantiated_set),
            ));
            for (original_name, generated_name) in param_def_with_set
                .params
                .iter()
                .zip(generated_names_for_current_group.iter())
            {
                original_param_to_forall_obj.insert(
                    original_name.clone(),
                    Obj::Identifier(Identifier::new(generated_name.clone())),
                );
            }
            flat_index = next_flat_index;
        }
        let forall_ret_set = self
            .inst_obj(fn_set.ret_set.as_ref(), &original_param_to_forall_obj)
            .map_err(|inst_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!("{}: failed to instantiate generated return set", context),
                    Some(inst_error.into()),
                    vec![],
                ))
            })?;
        let forall_args: Vec<Obj> = param_names
            .iter()
            .map(|param_name| {
                original_param_to_forall_obj
                    .get(param_name)
                    .unwrap()
                    .clone()
            })
            .collect();
        let forall_element_obj = Obj::Identifier(Identifier::new(forall_element_name.clone()));
        let arg_domain_factors: Vec<Obj> = forall_param_defs_with_type
            .iter()
            .map(|param_def_with_type| match &param_def_with_type.param_type {
                ParamType::Obj(obj) => obj.clone(),
                _ => unreachable!(),
            })
            .collect();
        let forall_arg_dom = if param_names.len() == 1 {
            arg_domain_factors[0].clone()
        } else {
            Obj::Cart(Cart::new(arg_domain_factors))
        };
        let forall_element_cart_set =
            Obj::Cart(Cart::new(vec![forall_arg_dom, forall_ret_set.clone()]));
        let forall_shape = Fact::ForallFact(ForallFact::new(
            vec![ParamGroupWithParamType::new(
                vec![forall_element_name.clone()],
                ParamType::Obj(function.clone()),
            )],
            vec![],
            vec![
                ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact::new(
                    forall_element_obj.clone(),
                    forall_element_cart_set,
                    line_file.clone(),
                ))),
                ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    Obj::TupleDim(TupleDim::new(forall_element_obj.clone())),
                    Obj::Number(Number::new("2".to_string())),
                    line_file.clone(),
                ))),
            ],
            line_file.clone(),
        ));
        let forall_z_obj = Obj::Identifier(Identifier::new(forall_z_name.clone()));
        let pair_in_fn = if param_names.len() == 1 {
            Obj::Tuple(Tuple::new(vec![forall_args[0].clone(), forall_z_obj]))
        } else {
            Obj::Tuple(Tuple::new(vec![
                Obj::Tuple(Tuple::new(forall_args)),
                forall_z_obj,
            ]))
        };
        let forall_in = Fact::ForallFact(ForallFact::new(
            vec![ParamGroupWithParamType::new(
                vec![forall_element_name],
                ParamType::Obj(function.clone()),
            )],
            vec![],
            vec![ExistOrAndChainAtomicFact::ExistFact(ExistFact::new(
                {
                    let mut exist_param_defs = forall_param_defs_with_type;
                    exist_param_defs.push(ParamGroupWithParamType::new(
                        vec![forall_z_name],
                        ParamType::Obj(forall_ret_set),
                    ));
                    exist_param_defs
                },
                {
                    let mut facts: Vec<OrAndChainAtomicFact> =
                        Vec::with_capacity(fn_set.dom_facts.len() + 1);
                    for dom_fact in fn_set.dom_facts.iter() {
                        facts.push(
                            self.inst_or_and_chain_atomic_fact(
                                dom_fact,
                                &original_param_to_forall_obj,
                            )
                            .map_err(|inst_error| {
                                RuntimeError::from(
                                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                        stmt_exec.clone(),
                                        format!(
                                            "{}: failed to instantiate generated domain fact",
                                            context
                                        ),
                                        Some(inst_error.into()),
                                        vec![],
                                    ),
                                )
                            })?,
                        );
                    }
                    facts.push(OrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
                        EqualFact::new(forall_element_obj, pair_in_fn, line_file.clone()),
                    )));
                    facts
                },
                line_file.clone(),
            ))],
            line_file.clone(),
        ));

        let mut generated_exist_names = self
            .generate_random_unused_names(param_names.len() + 2)
            .into_iter();
        let exist_element_name = generated_exist_names.next().unwrap();
        let exist_z_name = generated_exist_names.next().unwrap();
        let generated_exist_param_names: Vec<String> = generated_exist_names.collect();
        let mut original_param_to_exist_obj: HashMap<String, Obj> =
            HashMap::with_capacity(param_names.len());
        let mut exist_param_defs_with_type: Vec<ParamGroupWithParamType> =
            Vec::with_capacity(fn_set.params_def_with_set.len());
        let mut exist_flat_index: usize = 0;
        for param_def_with_set in fn_set.params_def_with_set.iter() {
            let next_flat_index = exist_flat_index + param_def_with_set.params.len();
            let generated_names_for_current_group =
                generated_exist_param_names[exist_flat_index..next_flat_index].to_vec();
            let instantiated_set = self
                .inst_obj(&param_def_with_set.set, &original_param_to_exist_obj)
                .map_err(|inst_error| {
                    RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec.clone(),
                        format!("{}: failed to instantiate witness parameter set", context),
                        Some(inst_error.into()),
                        vec![],
                    ))
                })?;
            exist_param_defs_with_type.push(ParamGroupWithParamType::new(
                generated_names_for_current_group.clone(),
                ParamType::Obj(instantiated_set),
            ));
            for (original_name, generated_name) in param_def_with_set
                .params
                .iter()
                .zip(generated_names_for_current_group.iter())
            {
                original_param_to_exist_obj.insert(
                    original_name.clone(),
                    Obj::Identifier(Identifier::new(generated_name.clone())),
                );
            }
            exist_flat_index = next_flat_index;
        }
        let exist_ret_set = self
            .inst_obj(fn_set.ret_set.as_ref(), &original_param_to_exist_obj)
            .map_err(|inst_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!("{}: failed to instantiate witness return set", context),
                    Some(inst_error.into()),
                    vec![],
                ))
            })?;
        let exist_args: Vec<Obj> = param_names
            .iter()
            .map(|param_name| original_param_to_exist_obj.get(param_name).unwrap().clone())
            .collect();
        let exist_element_obj = Obj::Identifier(Identifier::new(exist_element_name.clone()));
        let exist_z_obj = Obj::Identifier(Identifier::new(exist_z_name.clone()));
        let exist_pair = if param_names.len() == 1 {
            Obj::Tuple(Tuple::new(vec![exist_args[0].clone(), exist_z_obj]))
        } else {
            Obj::Tuple(Tuple::new(vec![
                Obj::Tuple(Tuple::new(exist_args)),
                exist_z_obj,
            ]))
        };
        let exist_fact = ExistFact::new(
            vec![
                ParamGroupWithParamType::new(
                    vec![exist_element_name],
                    ParamType::Obj(function.clone()),
                ),
                ParamGroupWithParamType::new(vec![exist_z_name], ParamType::Obj(exist_ret_set)),
            ],
            vec![OrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
                EqualFact::new(exist_element_obj, exist_pair, line_file.clone()),
            ))],
            line_file.clone(),
        );
        let forall_exist = Fact::ForallFact(ForallFact::new(
            exist_param_defs_with_type,
            {
                let mut dom_facts: Vec<ExistOrAndChainAtomicFact> =
                    Vec::with_capacity(fn_set.dom_facts.len());
                for dom_fact in fn_set.dom_facts.iter() {
                    dom_facts.push(
                        self.inst_or_and_chain_atomic_fact(dom_fact, &original_param_to_exist_obj)
                            .map_err(|inst_error| {
                                RuntimeError::from(
                                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                        stmt_exec.clone(),
                                        format!(
                                            "{}: failed to instantiate witness domain fact",
                                            context
                                        ),
                                        Some(inst_error.into()),
                                        vec![],
                                    ),
                                )
                            })?
                            .to_exist_or_and_chain_atomic_fact(),
                    );
                }
                dom_facts
            },
            vec![ExistOrAndChainAtomicFact::ExistFact(exist_fact)],
            line_file.clone(),
        ));

        let unique_names = self.generate_random_unused_names(2);
        let unique_x1_name = unique_names[0].clone();
        let unique_x2_name = unique_names[1].clone();
        let unique_x1_obj = Obj::Identifier(Identifier::new(unique_x1_name.clone()));
        let unique_x2_obj = Obj::Identifier(Identifier::new(unique_x2_name.clone()));
        let unique_param_group_sets: Vec<Obj> = fn_set
            .params_def_with_set
            .iter()
            .map(|param_def_with_set| param_def_with_set.set.clone())
            .collect();
        let unique_arg_dom = if param_names.len() == 1 {
            unique_param_group_sets[0].clone()
        } else {
            Obj::Cart(Cart::new(unique_param_group_sets))
        };
        let unique_element_cart_set = Obj::Cart(Cart::new(vec![
            unique_arg_dom,
            fn_set.ret_set.as_ref().clone(),
        ]));
        // 与手写标准一致：dom 为两元在图集内且首分量相同，then 仅为 x1 = x2
        let forall_unique = Fact::ForallFact(ForallFact::new(
            vec![ParamGroupWithParamType::new(
                vec![unique_x1_name, unique_x2_name],
                ParamType::Obj(function.clone()),
            )],
            vec![
                ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact::new(
                    unique_x1_obj.clone(),
                    unique_element_cart_set.clone(),
                    line_file.clone(),
                ))),
                ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact::new(
                    unique_x2_obj.clone(),
                    unique_element_cart_set.clone(),
                    line_file.clone(),
                ))),
                ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    Obj::ObjAtIndex(ObjAtIndex::new(
                        unique_x1_obj.clone(),
                        Obj::Number(Number::new("1".to_string())),
                    )),
                    Obj::ObjAtIndex(ObjAtIndex::new(
                        unique_x2_obj.clone(),
                        Obj::Number(Number::new("1".to_string())),
                    )),
                    line_file.clone(),
                ))),
            ],
            vec![ExistOrAndChainAtomicFact::AtomicFact(
                AtomicFact::EqualFact(EqualFact::new(
                    unique_x1_obj,
                    unique_x2_obj,
                    line_file.clone(),
                )),
            )],
            line_file.clone(),
        ));

        Ok((forall_shape, forall_in, forall_exist, forall_unique))
    }

    /// `by fn`：在本地环境中占位（不另从知识库证明），刻画事实在主环境登记。
    fn exec_by_fn_stmt_verify_process(&mut self) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_by_fn_stmt_store_process(
        &mut self,
        stmt_exec: &Stmt,
        forall_shape: Fact,
        forall_in: Fact,
        forall_exist: Fact,
        forall_unique: Fact,
    ) -> Result<InferResult, RuntimeError> {
        // `store_fact...` on forall facts already feeds the stored fact back through `infer`,
        // so avoid pre-recording the same fact here or JSON `infer_facts` will show duplicates.
        let mut infer_result = InferResult::new();
        let infer_shape = self
            .store_fact_without_well_defined_verified_and_infer(forall_shape)
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store cart/tuple shape characterization fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_shape);
        let infer_in = self
            .store_fact_without_well_defined_verified_and_infer(forall_in)
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store graph-element characterization fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_in);

        let infer_exist = self
            .store_fact_without_well_defined_verified_and_infer(forall_exist)
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store element characterization fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_exist);

        let infer_unique = self
            .store_fact_without_forall_coverage_check_and_infer(forall_unique)
            .map_err(|store_fact_error| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn: failed to store uniqueness characterization fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_unique);

        Ok(infer_result)
    }

    pub fn exec_by_fn_stmt(&mut self, stmt: &ByFnStmt) -> Result<StmtExecResult, RuntimeError> {
        let stmt_exec = stmt.clone().into();

        let fn_set = match self.get_cloned_object_in_fn_set(&stmt.function) {
            Some(fs) => fs,
            None => {
                return Err(RuntimeError::ExecStmtError(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec,
                        format!(
                            "by fn: `{}` is not known to belong to a fn set",
                            stmt.function
                        ),
                        None,
                        vec![],
                    ),
                ));
            }
        };

        let (forall_shape, forall_in, forall_exist, forall_unique) = self
            .build_fn_characterization_facts(
                &stmt.function,
                &fn_set,
                &stmt.line_file,
                &stmt_exec,
                "by fn",
            )?;

        self.run_in_local_env(|rt| rt.exec_by_fn_stmt_verify_process())?;

        let infer_result = self.exec_by_fn_stmt_store_process(
            &stmt_exec,
            forall_shape,
            forall_in,
            forall_exist,
            forall_unique,
        )?;

        Ok(StmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![]),
        ))
    }

    fn exec_by_fn_set_stmt_verify_process(
        &mut self,
        stmt_exec: &Stmt,
        forall_shape: &Fact,
        forall_in: &Fact,
        forall_exist: &Fact,
        forall_unique: &Fact,
    ) -> Result<Vec<StmtExecResult>, RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        let verify_shape_fact = self
            .verify_fact_return_err_if_not_true(forall_shape, &verify_state)
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove cart/tuple shape characterization `{}`",
                        forall_shape
                    ),
                    Some(verify_error.into()),
                    vec![],
                ))
            })?;
        let verify_random_param_fact = self
            .verify_fact_return_err_if_not_true(forall_in, &verify_state)
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove graph-element characterization `{}`",
                        forall_in
                    ),
                    Some(verify_error.into()),
                    vec![],
                ))
            })?;
        let verify_param_to_element_fact = self
            .verify_fact_return_err_if_not_true(forall_exist, &verify_state)
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove graph-coverage characterization `{}`",
                        forall_exist
                    ),
                    Some(verify_error.into()),
                    vec![],
                ))
            })?;
        let verify_uniqueness_fact = self
            .verify_fact_return_err_if_not_true(forall_unique, &verify_state)
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove graph-uniqueness characterization `{}`",
                        forall_unique
                    ),
                    Some(verify_error.into()),
                    vec![],
                ))
            })?;

        Ok(vec![
            verify_shape_fact,
            verify_random_param_fact,
            verify_param_to_element_fact,
            verify_uniqueness_fact,
        ])
    }

    fn exec_by_fn_set_stmt_store_process(
        &mut self,
        stmt: &ByFnSetStmt,
        stmt_exec: &Stmt,
    ) -> Result<InferResult, RuntimeError> {
        let membership_fact = AtomicFact::InFact(InFact::new(
            stmt.func.clone(),
            Obj::FnSet(stmt.fn_set.clone()),
            stmt.line_file.clone(),
        ));
        self.store_atomic_fact_without_well_defined_verified_and_infer(membership_fact)
            .map_err(|store_fact_error| {
                RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by fn set: failed to store membership fact".to_string(),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })
    }

    pub fn exec_by_fn_set_stmt(
        &mut self,
        stmt: &ByFnSetStmt,
    ) -> Result<StmtExecResult, RuntimeError> {
        let stmt_exec = stmt.clone().into();
        let (forall_shape, forall_in, forall_exist, forall_unique) = self
            .build_fn_characterization_facts(
                &stmt.func,
                &stmt.fn_set,
                &stmt.line_file,
                &stmt_exec,
                "by fn set",
            )?;

        let verify_inside_results = self.run_in_local_env(|rt| {
            rt.exec_by_fn_set_stmt_verify_process(
                &stmt_exec,
                &forall_shape,
                &forall_in,
                &forall_exist,
                &forall_unique,
            )
        })?;

        let infer_result = self.exec_by_fn_set_stmt_store_process(stmt, &stmt_exec)?;

        Ok(StmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(stmt_exec, infer_result, verify_inside_results),
        ))
    }
}
