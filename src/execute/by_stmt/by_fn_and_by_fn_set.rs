use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    fn build_fn_characterization_facts(
        &mut self,
        function: &Obj,
        fn_body: &FnSetBody,
        line_file: &LineFile,
        stmt_exec: &Stmt,
        context: &str,
    ) -> Result<(Fact, Fact, Fact, Fact), RuntimeError> {
        let param_names = ParamGroupWithSet::collect_param_names(&fn_body.params_def_with_set);
        if param_names.is_empty() {
            return Err(short_exec_error(
                stmt_exec.clone(),
                format!("{}: fn set has no parameters", context),
                None,
                vec![],
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
            Vec::with_capacity(fn_body.params_def_with_set.len());
        let mut flat_index: usize = 0;
        for param_def_with_set in fn_body.params_def_with_set.iter() {
            let next_flat_index = flat_index + param_def_with_set.params.len();
            let generated_names_for_current_group =
                generated_forall_param_names[flat_index..next_flat_index].to_vec();
            let instantiated_type = match &param_def_with_set.param_type {
                ParamGroupWithSetTypeEnum::Set(set) => ParamType::Obj(
                    self.inst_obj(set, &original_param_to_forall_obj, ParamObjType::FnSet)
                        .map_err(|inst_error| {
                            short_exec_error(
                                stmt_exec.clone(),
                                format!(
                                    "{}: failed to instantiate generated parameter set",
                                    context
                                ),
                                Some(inst_error),
                                vec![],
                            )
                        })?,
                ),
                ParamGroupWithSetTypeEnum::Struct(struct_ty) => self
                    .inst_param_type(
                        &ParamType::Struct(struct_ty.clone()),
                        &original_param_to_forall_obj,
                        ParamObjType::FnSet,
                    )
                    .map_err(|inst_error| {
                        short_exec_error(
                            stmt_exec.clone(),
                            format!(
                                "{}: failed to instantiate generated struct parameter type",
                                context
                            ),
                            Some(inst_error),
                            vec![],
                        )
                    })?,
            };
            forall_param_defs_with_type.push(ParamGroupWithParamType::new(
                generated_names_for_current_group.clone(),
                instantiated_type,
            ));
            for (original_name, generated_name) in param_def_with_set
                .params
                .iter()
                .zip(generated_names_for_current_group.iter())
            {
                original_param_to_forall_obj.insert(
                    original_name.clone(),
                    obj_for_bound_param_in_scope(generated_name.clone(), ParamObjType::FnSet),
                );
            }
            flat_index = next_flat_index;
        }
        // Exist body binds the same generated names as `Exist` params (~3), not FnSet (~5).
        let original_param_to_exist_inner: HashMap<String, Obj> = original_param_to_forall_obj
            .iter()
            .filter_map(|(orig, obj)| {
                if let Obj::Atom(AtomObj::FnSet(p)) = obj {
                    Some((
                        orig.clone(),
                        obj_for_bound_param_in_scope(p.name.clone(), ParamObjType::Exist),
                    ))
                } else {
                    None
                }
            })
            .collect();
        let forall_ret_set = self
            .inst_obj(
                fn_body.ret_set.as_ref(),
                &original_param_to_forall_obj,
                ParamObjType::FnSet,
            )
            .map_err(|inst_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!("{}: failed to instantiate generated return set", context),
                    Some(inst_error),
                    vec![],
                )
            })?;
        let forall_args_exist: Vec<Obj> = param_names
            .iter()
            .map(|param_name| {
                original_param_to_exist_inner
                    .get(param_name)
                    .unwrap()
                    .clone()
            })
            .collect();
        let forall_element_obj: Obj =
            obj_for_bound_param_in_scope(forall_element_name.clone(), ParamObjType::Forall);
        let mut forall_element_cart_factors: Vec<Obj> = Vec::with_capacity(param_names.len() + 1);
        for param_def_with_type in forall_param_defs_with_type.iter() {
            match &param_def_with_type.param_type {
                ParamType::Obj(obj) => {
                    for _ in param_def_with_type.params.iter() {
                        forall_element_cart_factors.push(obj.clone());
                    }
                }
                _ => unreachable!(),
            }
        }
        forall_element_cart_factors.push(forall_ret_set.clone());
        let forall_element_cart_set = Cart::new(forall_element_cart_factors).into();
        let forall_shape = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![forall_element_name.clone()],
                ParamType::Obj(function.clone()),
            )]),
            vec![],
            vec![
                InFact::new(
                    forall_element_obj.clone(),
                    forall_element_cart_set,
                    line_file.clone(),
                )
                .into(),
                EqualFact::new(
                    TupleDim::new(forall_element_obj.clone()).into(),
                    Number::new((param_names.len() + 1).to_string()).into(),
                    line_file.clone(),
                )
                .into(),
            ],
            line_file.clone(),
        )?
        .into();
        let forall_z_obj = obj_for_bound_param_in_scope(forall_z_name.clone(), ParamObjType::Exist);
        let mut tuple_in_fn = forall_args_exist;
        tuple_in_fn.push(forall_z_obj);
        let tuple_in_fn = Tuple::new(tuple_in_fn).into();
        let forall_in = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![forall_element_name],
                ParamType::Obj(function.clone()),
            )]),
            vec![],
            vec![ExistFactEnum::ExistFact(ExistFactBody::new(
                ParamDefWithType::new({
                    let mut exist_param_defs = forall_param_defs_with_type;
                    exist_param_defs.push(ParamGroupWithParamType::new(
                        vec![forall_z_name],
                        ParamType::Obj(forall_ret_set),
                    ));
                    exist_param_defs
                }),
                {
                    let mut facts: Vec<ExistBodyFact> =
                        Vec::with_capacity(fn_body.dom_facts.len() + 1);
                    for dom_fact in fn_body.dom_facts.iter() {
                        facts.push(
                            self.inst_or_and_chain_atomic_fact(
                                dom_fact,
                                &original_param_to_exist_inner,
                                ParamObjType::FnSet,
                                None,
                            )
                            .map_err(|inst_error| {
                                short_exec_error(
                                    stmt_exec.clone(),
                                    format!(
                                        "{}: failed to instantiate generated domain fact",
                                        context
                                    ),
                                    Some(inst_error),
                                    vec![],
                                )
                            })?
                            .into(),
                        );
                    }
                    facts.push(
                        EqualFact::new(forall_element_obj, tuple_in_fn, line_file.clone()).into(),
                    );
                    facts
                },
                line_file.clone(),
            )?)
            .into()],
            line_file.clone(),
        )?
        .into();

        let mut generated_exist_names = self
            .generate_random_unused_names(param_names.len() + 2)
            .into_iter();
        let exist_element_name = generated_exist_names.next().unwrap();
        let exist_z_name = generated_exist_names.next().unwrap();
        let generated_exist_param_names: Vec<String> = generated_exist_names.collect();
        let mut original_param_to_exist_obj: HashMap<String, Obj> =
            HashMap::with_capacity(param_names.len());
        let mut exist_param_defs_with_type: Vec<ParamGroupWithParamType> =
            Vec::with_capacity(fn_body.params_def_with_set.len());
        let mut exist_flat_index: usize = 0;
        for param_def_with_set in fn_body.params_def_with_set.iter() {
            let next_flat_index = exist_flat_index + param_def_with_set.params.len();
            let generated_names_for_current_group =
                generated_exist_param_names[exist_flat_index..next_flat_index].to_vec();
            let instantiated_type = match &param_def_with_set.param_type {
                ParamGroupWithSetTypeEnum::Set(set) => ParamType::Obj(
                    self.inst_obj(set, &original_param_to_exist_obj, ParamObjType::FnSet)
                        .map_err(|inst_error| {
                            short_exec_error(
                                stmt_exec.clone(),
                                format!("{}: failed to instantiate witness parameter set", context),
                                Some(inst_error),
                                vec![],
                            )
                        })?,
                ),
                ParamGroupWithSetTypeEnum::Struct(struct_ty) => self
                    .inst_param_type(
                        &ParamType::Struct(struct_ty.clone()),
                        &original_param_to_exist_obj,
                        ParamObjType::FnSet,
                    )
                    .map_err(|inst_error| {
                        short_exec_error(
                            stmt_exec.clone(),
                            format!(
                                "{}: failed to instantiate witness struct parameter type",
                                context
                            ),
                            Some(inst_error),
                            vec![],
                        )
                    })?,
            };
            exist_param_defs_with_type.push(ParamGroupWithParamType::new(
                generated_names_for_current_group.clone(),
                instantiated_type,
            ));
            for (original_name, generated_name) in param_def_with_set
                .params
                .iter()
                .zip(generated_names_for_current_group.iter())
            {
                original_param_to_exist_obj.insert(
                    original_name.clone(),
                    obj_for_bound_param_in_scope(generated_name.clone(), ParamObjType::FnSet),
                );
            }
            exist_flat_index = next_flat_index;
        }
        // Outer `forall_exist` quantifies fn parameters as Forall (~1), not FnSet (~5).
        let original_param_to_forall_witness: HashMap<String, Obj> = original_param_to_exist_obj
            .iter()
            .filter_map(|(orig, obj)| {
                if let Obj::Atom(AtomObj::FnSet(p)) = obj {
                    Some((
                        orig.clone(),
                        obj_for_bound_param_in_scope(p.name.clone(), ParamObjType::Forall),
                    ))
                } else {
                    None
                }
            })
            .collect();
        let exist_ret_set = self
            .inst_obj(
                fn_body.ret_set.as_ref(),
                &original_param_to_exist_obj,
                ParamObjType::FnSet,
            )
            .map_err(|inst_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!("{}: failed to instantiate witness return set", context),
                    Some(inst_error),
                    vec![],
                )
            })?;
        let exist_args_for_pair: Vec<Obj> = param_names
            .iter()
            .map(|param_name| {
                original_param_to_forall_witness
                    .get(param_name)
                    .unwrap()
                    .clone()
            })
            .collect();
        let exist_element_obj =
            obj_for_bound_param_in_scope(exist_element_name.clone(), ParamObjType::Exist);
        let exist_z_obj = obj_for_bound_param_in_scope(exist_z_name.clone(), ParamObjType::Exist);
        let mut exist_tuple = exist_args_for_pair;
        exist_tuple.push(exist_z_obj);
        let exist_tuple = Tuple::new(exist_tuple).into();
        let exist_fact = ExistFactEnum::ExistFact(ExistFactBody::new(
            ParamDefWithType::new(vec![
                ParamGroupWithParamType::new(
                    vec![exist_element_name],
                    ParamType::Obj(function.clone()),
                ),
                ParamGroupWithParamType::new(vec![exist_z_name], ParamType::Obj(exist_ret_set)),
            ]),
            vec![EqualFact::new(exist_element_obj, exist_tuple, line_file.clone()).into()],
            line_file.clone(),
        )?);
        let forall_exist = ForallFact::new(
            ParamDefWithType::new(exist_param_defs_with_type),
            {
                let mut dom_facts: Vec<Fact> = Vec::with_capacity(fn_body.dom_facts.len());
                for dom_fact in fn_body.dom_facts.iter() {
                    dom_facts.push(
                        self.inst_or_and_chain_atomic_fact(
                            dom_fact,
                            &original_param_to_forall_witness,
                            ParamObjType::FnSet,
                            None,
                        )
                        .map_err(|inst_error| {
                            short_exec_error(
                                stmt_exec.clone(),
                                format!("{}: failed to instantiate witness domain fact", context),
                                Some(inst_error),
                                vec![],
                            )
                        })?
                        .into(),
                    );
                }
                dom_facts
            },
            vec![exist_fact.into()],
            line_file.clone(),
        )?
        .into();

        let unique_names = self.generate_random_unused_names(2);
        let unique_x1_name = unique_names[0].clone();
        let unique_x2_name = unique_names[1].clone();
        let unique_x1_obj: Obj =
            obj_for_bound_param_in_scope(unique_x1_name.clone(), ParamObjType::Forall);
        let unique_x2_obj: Obj =
            obj_for_bound_param_in_scope(unique_x2_name.clone(), ParamObjType::Forall);
        let mut unique_element_cart_factors: Vec<Obj> = Vec::with_capacity(param_names.len() + 1);
        for param_def_with_set in fn_body.params_def_with_set.iter() {
            let Some(set) = param_def_with_set.set_obj() else {
                return Err(short_exec_error(
                    stmt_exec.clone(),
                    "by fn set: struct parameters cannot be unfolded as cartesian graph factors yet".to_string(),
                    None,
                    vec![],
                ));
            };
            for _ in param_def_with_set.params.iter() {
                unique_element_cart_factors.push(set.clone());
            }
        }
        unique_element_cart_factors.push(fn_body.ret_set.as_ref().clone());
        let unique_element_cart_set: Obj = Cart::new(unique_element_cart_factors).into();
        let mut unique_dom_facts: Vec<Fact> = Vec::with_capacity(param_names.len() + 2);
        unique_dom_facts.push(
            InFact::new(
                unique_x1_obj.clone(),
                unique_element_cart_set.clone(),
                line_file.clone(),
            )
            .into(),
        );
        unique_dom_facts.push(
            InFact::new(
                unique_x2_obj.clone(),
                unique_element_cart_set.clone(),
                line_file.clone(),
            )
            .into(),
        );
        for index in 1..=param_names.len() {
            unique_dom_facts.push(
                EqualFact::new(
                    ObjAtIndex::new(unique_x1_obj.clone(), Number::new(index.to_string()).into())
                        .into(),
                    ObjAtIndex::new(unique_x2_obj.clone(), Number::new(index.to_string()).into())
                        .into(),
                    line_file.clone(),
                )
                .into(),
            );
        }
        let forall_unique = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![unique_x1_name, unique_x2_name],
                ParamType::Obj(function.clone()),
            )]),
            unique_dom_facts,
            vec![EqualFact::new(unique_x1_obj, unique_x2_obj, line_file.clone()).into()],
            line_file.clone(),
        )?
        .into();

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
            .verify_well_defined_and_store_and_infer_with_default_verify_state(forall_shape)
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by fn: failed to store cart/tuple shape characterization fact".to_string(),
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        infer_result.new_infer_result_inside(infer_shape);
        let infer_in = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(forall_in)
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by fn: failed to store graph-element characterization fact".to_string(),
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        infer_result.new_infer_result_inside(infer_in);

        let infer_exist = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(forall_exist)
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by fn: failed to store element characterization fact".to_string(),
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        infer_result.new_infer_result_inside(infer_exist);

        let infer_unique = self
            .store_fact_without_forall_coverage_check_and_infer(forall_unique)
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by fn: failed to store uniqueness characterization fact".to_string(),
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        infer_result.new_infer_result_inside(infer_unique);

        Ok(infer_result)
    }

    pub fn exec_by_fn_stmt(&mut self, stmt: &ByFnStmt) -> Result<StmtResult, RuntimeError> {
        let stmt_exec: Stmt = stmt.clone().into();

        let fn_set = match self.get_cloned_object_in_fn_set(&stmt.function) {
            Some(fs) => fs,
            None => {
                return Err(short_exec_error(
                    stmt_exec,
                    format!(
                        "by fn: `{}` is not known to belong to a fn set",
                        stmt.function
                    ),
                    None,
                    vec![],
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

        Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
    }

    fn exec_by_fn_set_stmt_verify_process(
        &mut self,
        stmt_exec: &Stmt,
        forall_shape: &Fact,
        forall_in: &Fact,
        forall_exist: &Fact,
        forall_unique: &Fact,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        let verify_shape_fact = self
            .verify_fact_return_err_if_not_true(forall_shape, &verify_state)
            .map_err(|verify_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove cart/tuple shape characterization `{}`",
                        forall_shape
                    ),
                    Some(verify_error),
                    vec![],
                )
            })?;
        let verify_random_param_fact = self
            .verify_fact_return_err_if_not_true(forall_in, &verify_state)
            .map_err(|verify_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove graph-element characterization `{}`",
                        forall_in
                    ),
                    Some(verify_error),
                    vec![],
                )
            })?;
        let verify_param_to_element_fact = self
            .verify_fact_return_err_if_not_true(forall_exist, &verify_state)
            .map_err(|verify_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove graph-coverage characterization `{}`",
                        forall_exist
                    ),
                    Some(verify_error),
                    vec![],
                )
            })?;
        let verify_uniqueness_fact = self
            .verify_fact_return_err_if_not_true(forall_unique, &verify_state)
            .map_err(|verify_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by fn set: failed to prove graph-uniqueness characterization `{}`",
                        forall_unique
                    ),
                    Some(verify_error),
                    vec![],
                )
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
        let membership_fact = InFact::new(
            stmt.func.clone(),
            stmt.fn_set.clone().into(),
            stmt.line_file.clone(),
        )
        .into();
        self.store_atomic_fact_without_well_defined_verified_and_infer(membership_fact)
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by fn set: failed to store membership fact".to_string(),
                    Some(store_fact_error),
                    vec![],
                )
            })
    }

    pub fn exec_by_fn_set_stmt(&mut self, stmt: &ByFnSetStmt) -> Result<StmtResult, RuntimeError> {
        let stmt_exec: Stmt = stmt.clone().into();
        let (forall_shape, forall_in, forall_exist, forall_unique) = self
            .build_fn_characterization_facts(
                &stmt.func,
                &stmt.fn_set.body,
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

        Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, verify_inside_results)).into())
    }
}
