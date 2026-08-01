use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_def_template_stmt(
        &mut self,
        def_template_stmt: &DefTemplateStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.def_template_stmt_check_well_defined(def_template_stmt))
            .map_err(|e| {
                exec_stmt_error_with_stmt_and_cause(def_template_stmt.clone().into(), e)
            })?;
        self.store_def_template(def_template_stmt)?;
        Ok(NonFactualStmtSuccess::new_with_stmt(def_template_stmt.clone().into()).into())
    }

    fn def_template_stmt_check_well_defined(
        &mut self,
        def_template_stmt: &DefTemplateStmt,
    ) -> Result<(), RuntimeError> {
        let verify_state = UseContextVerifyState::new(0, false);
        self.define_params_with_type(
            &def_template_stmt.template_arg_def,
            false,
            ParamObjType::DefHeader,
        )?;

        for dom_fact in def_template_stmt.template_arg_dom.iter() {
            self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                dom_fact,
                &verify_state,
            )?;
        }

        let template_body_stmt = def_template_stmt.template_def_stmt.to_stmt();
        self.exec_stmt(&template_body_stmt)?;
        Ok(())
    }

    pub fn materialize_instantiated_template_obj(
        &mut self,
        template_obj: &InstantiatedTemplateObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let instance_name = template_obj.surface_name();
        if self.is_name_used_for_identifier(&instance_name) {
            return Ok(());
        }
        let template_name = template_obj.template_name.to_string();
        let def = self
            .get_template_definition_by_name(&template_name)
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "template `{}` is not defined",
                        template_name
                    )),
                ))
            })?;

        if template_obj.args.len() != def.template_arg_def.number_of_params() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "template `{}` expects {} argument(s), got {}",
                    template_obj.template_name,
                    def.template_arg_def.number_of_params(),
                    template_obj.args.len()
                )),
            )));
        }

        for arg in template_obj.args.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let verify_args_result = self.verify_args_satisfy_param_def_flat_types(
            &def.template_arg_def,
            &template_obj.args,
            verify_state,
            ParamObjType::DefHeader,
        )?;
        if verify_args_result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "failed to verify template `{}` arguments satisfy parameter types",
                    template_obj.template_name
                )),
            )));
        }

        let param_to_arg_map = def
            .template_arg_def
            .param_defs_and_args_to_param_to_arg_map(&template_obj.args);

        for dom_fact in def.template_arg_dom.iter() {
            let instantiated_dom_fact = self.inst_or_and_chain_atomic_fact(
                dom_fact,
                &param_to_arg_map,
                ParamObjType::DefHeader,
                None,
            )?;
            let verify_result =
                self.verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "failed to verify template `{}` domain fact:\n{}",
                        template_obj.template_name, instantiated_dom_fact
                    )),
                )));
            }
            self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                instantiated_dom_fact,
            )?;
        }

        let stmt = self.inst_template_body_stmt(
            &def.template_def_stmt,
            &param_to_arg_map,
            &instance_name,
            &template_obj.declaration_binding(),
            &def.line_file,
        )?;
        let instance_identifier = self.declared_identifier_obj(&instance_name);
        // Register the public template application as an alias before the
        // instantiated body stores derived facts. For a selected function,
        // this lets its unique-existence property normalize directly to calls
        // such as `\selected<T>(x)` instead of remaining attached only to the
        // hidden materialized identifier.
        self.store_atomic_fact_without_well_defined_verified_and_infer(
            EqualFact::new(
                template_obj.clone().into(),
                instance_identifier.clone(),
                def.line_file.clone(),
            )
            .into(),
        )?;
        // The template body was verified once with symbolic parameters when the
        // template was declared. Header validation above plus capture-avoiding
        // substitution preserves that result, so only commit the instantiated
        // statement's environment effects here.
        self.exec_preverified_stmt_affect_environment_only(&stmt)?;
        if let Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(case_stmt)) = &stmt {
            self.store_template_surface_case_equations(case_stmt, template_obj)?;
        }
        if let Stmt::DefObjStmt(DefObjStmt::HaveFnByInducStmt(recursive_stmt)) = &stmt {
            let flat = recursive_stmt.to_have_fn_equal_case_by_case_stmt();
            self.store_template_surface_case_equations(&flat, template_obj)?;
        }
        if let Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(choice_stmt)) = &stmt {
            // The generic choice theorem was checked at template declaration.
            // Register its instantiated property under the public template
            // application as well as the hidden materialized identifier.
            self.store_instantiated_template_choice_property(choice_stmt, template_obj)?;
        }
        if let Some(set_builder) = self.get_obj_equal_to_set_builder(&instance_name) {
            // Keep the template surface object connected to a materialized
            // set-builder value. Example: after `template<T>: have selected =
            // {x T: P(x)}`, membership in `\selected<T>` can expose `P(x)`.
            self.store_known_set_builder_obj(
                &template_obj.to_string(),
                set_builder,
                def.line_file.clone(),
            );
        }
        Ok(())
    }

    fn inst_template_body_stmt(
        &self,
        stmt: &TemplateDefEnum,
        param_to_arg_map: &HashMap<String, Obj>,
        instance_name: &str,
        instance_binding: &SymbolBinding,
        line_file: &LineFile,
    ) -> Result<Stmt, RuntimeError> {
        match stmt {
            TemplateDefEnum::HaveObjInNonemptySetStmt(s) => {
                let param_def = self.inst_single_result_param_def(
                    &s.param_def,
                    param_to_arg_map,
                    instance_binding,
                )?;
                Ok(HaveObjInNonemptySetOrParamTypeStmt::new(param_def, line_file.clone()).into())
            }
            TemplateDefEnum::HaveObjEqualStmt(s) => {
                let param_def = self.inst_single_result_param_def(
                    &s.param_def,
                    param_to_arg_map,
                    instance_binding,
                )?;
                let mut objs_equal_to = Vec::with_capacity(s.objs_equal_to.len());
                for obj in s.objs_equal_to.iter() {
                    objs_equal_to.push(self.inst_obj(
                        obj,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                    )?);
                }
                Ok(HaveObjEqualStmt::new(param_def, objs_equal_to, line_file.clone()).into())
            }
            TemplateDefEnum::HaveObjByExistFactsStmt(s) => {
                let body =
                    ExistFactBody::new(s.param_def.clone(), s.facts.clone(), s.line_file.clone())?;
                let exist_fact = self.inst_exist_fact(
                    &ExistFactEnum::ExistFact(body),
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file),
                )?;
                Ok(HaveByExistStmt::new(
                    vec![instance_name.to_string()],
                    vec![instance_binding.clone()],
                    exist_fact,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::TrustHaveStmt(s) => {
                let param_def = self.inst_single_result_param_def(
                    &s.param_def,
                    param_to_arg_map,
                    instance_binding,
                )?;
                let defined_bindings = s.param_def.collect_param_bindings();
                if defined_bindings.len() != 1 {
                    return Err(RuntimeError::from(InstantiateRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "template `trust have` body must define exactly one object".to_string(),
                        ),
                    )));
                }
                let defined_binding = &defined_bindings[0];
                let mut body_param_to_arg_map = param_to_arg_map.clone();
                insert_symbol_substitution(
                    &mut body_param_to_arg_map,
                    defined_binding,
                    Identifier::new_bound(instance_name.to_string(), instance_binding.as_ref())
                        .into(),
                );
                let mut facts = Vec::with_capacity(s.facts.len());
                for fact in s.facts.iter() {
                    facts.push(self.inst_fact(
                        fact,
                        &body_param_to_arg_map,
                        ParamObjType::DefHeader,
                        Some(line_file.clone()),
                    )?);
                }
                Ok(TrustHaveStmt::new(param_def, facts, line_file.clone()).into())
            }
            TemplateDefEnum::HaveByExistStmt(s) => {
                let exist_fact = self.inst_exist_fact(
                    &s.exist_fact_in_have_obj_st,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file),
                )?;
                Ok(HaveByExistStmt::new(
                    vec![instance_name.to_string()],
                    vec![instance_binding.clone()],
                    exist_fact,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveFnEqualStmt(s) => {
                let obj = self.inst_obj(
                    &s.equal_to_anonymous_fn.clone().into(),
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let Obj::AnonymousFn(anonymous_fn) = obj else {
                    return Err(RuntimeError::from(InstantiateRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "template function body did not instantiate to anonymous function"
                                .to_string(),
                        ),
                    )));
                };
                Ok(HaveFnEqualStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    anonymous_fn,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(s) => {
                let (fn_set_clause, body_map) =
                    self.inst_fn_set_clause(&s.fn_set_clause, param_to_arg_map)?;
                let mut cases = Vec::with_capacity(s.cases.len());
                for c in s.cases.iter() {
                    cases.push(self.inst_and_chain_atomic_fact(
                        c,
                        &body_map,
                        ParamObjType::DefHeader,
                        Some(line_file),
                    )?);
                }
                let mut equal_tos = Vec::with_capacity(s.equal_tos.len());
                for obj in s.equal_tos.iter() {
                    equal_tos.push(self.inst_obj(obj, &body_map, ParamObjType::DefHeader)?);
                }
                Ok(HaveFnEqualCaseByCaseStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    fn_set_clause,
                    cases,
                    equal_tos,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveFnByInducStmt(s) => {
                let (fn_set_clause, mut body_map) =
                    self.inst_fn_set_clause(&s.fn_set_clause, param_to_arg_map)?;
                insert_symbol_substitution(
                    &mut body_map,
                    &s.symbol_binding,
                    Identifier::new_bound(instance_name.to_string(), instance_binding.as_ref())
                        .into(),
                );
                let measure = self.inst_obj(&s.measure, &body_map, ParamObjType::DefHeader)?;
                let lower_bound =
                    self.inst_obj(&s.lower_bound, &body_map, ParamObjType::DefHeader)?;
                let mut cases = Vec::with_capacity(s.cases.len());
                for c in s.cases.iter() {
                    cases.push(self.inst_have_fn_by_induc_case(c, &body_map, line_file)?);
                }
                Ok(HaveFnByInducStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    fn_set_clause,
                    measure,
                    lower_bound,
                    cases,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(s) => {
                let forall = self.inst_forall_fact(
                    &s.forall,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file),
                )?;
                let mut proof_param_to_arg_map = param_to_arg_map.clone();
                for (source_binding, instantiated_binding) in s
                    .forall
                    .params_def_with_type
                    .collect_param_bindings()
                    .iter()
                    .zip(forall.params_def_with_type.collect_param_bindings().iter())
                {
                    insert_symbol_substitution(
                        &mut proof_param_to_arg_map,
                        source_binding,
                        obj_for_bound_param_in_scope(instantiated_binding, ParamObjType::Forall),
                    );
                }
                let prove_process = self.inst_template_proof_process(
                    &s.prove_process,
                    &proof_param_to_arg_map,
                    line_file,
                )?;
                Ok(HaveFnByForallExistUniqueStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    forall,
                    prove_process,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveTupleStmt(s) => {
                let index_binding = self.allocate_local_symbol_binding(s.index_name.clone())?;
                let mut body_map = param_to_arg_map.clone();
                insert_symbol_substitution(
                    &mut body_map,
                    &s.index_binding,
                    obj_for_bound_param_in_scope(&index_binding, ParamObjType::TupleIndex),
                );
                let dimension =
                    self.inst_obj(&s.dimension, param_to_arg_map, ParamObjType::DefHeader)?;
                let value = self.inst_obj(&s.value, &body_map, ParamObjType::TupleIndex)?;
                Ok(HaveTupleStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    s.index_name.clone(),
                    index_binding,
                    dimension,
                    value,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveCartStmt(s) => {
                let index_binding = self.allocate_local_symbol_binding(s.index_name.clone())?;
                let mut body_map = param_to_arg_map.clone();
                insert_symbol_substitution(
                    &mut body_map,
                    &s.index_binding,
                    obj_for_bound_param_in_scope(&index_binding, ParamObjType::CartIndex),
                );
                let dimension =
                    self.inst_obj(&s.dimension, param_to_arg_map, ParamObjType::DefHeader)?;
                let value = self.inst_obj(&s.value, &body_map, ParamObjType::CartIndex)?;
                Ok(HaveCartStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    s.index_name.clone(),
                    index_binding,
                    dimension,
                    value,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveSeqStmt(s) => {
                let index_binding = self.allocate_local_symbol_binding(s.index_name.clone())?;
                let mut body_map = param_to_arg_map.clone();
                insert_symbol_substitution(
                    &mut body_map,
                    &s.index_binding,
                    obj_for_bound_param_in_scope(&index_binding, ParamObjType::FnSet),
                );
                let set =
                    self.inst_obj(&s.seq_set.set, param_to_arg_map, ParamObjType::DefHeader)?;
                let value = self.inst_obj(&s.value, &body_map, ParamObjType::FnSet)?;
                Ok(HaveSeqStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    SeqSet::new(set),
                    s.index_name.clone(),
                    index_binding,
                    value,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveFiniteSeqStmt(s) => {
                let index_binding = self.allocate_local_symbol_binding(s.index_name.clone())?;
                let mut body_map = param_to_arg_map.clone();
                insert_symbol_substitution(
                    &mut body_map,
                    &s.index_binding,
                    obj_for_bound_param_in_scope(&index_binding, ParamObjType::FnSet),
                );
                let set = self.inst_obj(
                    &s.finite_seq_set.set,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let n = self.inst_obj(
                    &s.finite_seq_set.n,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let bound = self.inst_obj(&s.bound, param_to_arg_map, ParamObjType::DefHeader)?;
                let value = self.inst_obj(&s.value, &body_map, ParamObjType::FnSet)?;
                Ok(HaveFiniteSeqStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    FiniteSeqSet::new(set, n),
                    s.index_name.clone(),
                    index_binding,
                    bound,
                    value,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveMatrixStmt(s) => {
                let row_index_binding =
                    self.allocate_local_symbol_binding(s.row_index_name.clone())?;
                let col_index_binding =
                    self.allocate_local_symbol_binding(s.col_index_name.clone())?;
                let mut body_map = param_to_arg_map.clone();
                insert_symbol_substitution(
                    &mut body_map,
                    &s.row_index_binding,
                    obj_for_bound_param_in_scope(&row_index_binding, ParamObjType::FnSet),
                );
                insert_symbol_substitution(
                    &mut body_map,
                    &s.col_index_binding,
                    obj_for_bound_param_in_scope(&col_index_binding, ParamObjType::FnSet),
                );
                let set =
                    self.inst_obj(&s.matrix_set.set, param_to_arg_map, ParamObjType::DefHeader)?;
                let row_len = self.inst_obj(
                    &s.matrix_set.row_len,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let col_len = self.inst_obj(
                    &s.matrix_set.col_len,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let row_bound =
                    self.inst_obj(&s.row_bound, param_to_arg_map, ParamObjType::DefHeader)?;
                let col_bound =
                    self.inst_obj(&s.col_bound, param_to_arg_map, ParamObjType::DefHeader)?;
                let value = self.inst_obj(&s.value, &body_map, ParamObjType::FnSet)?;
                Ok(HaveMatrixStmt::new(
                    instance_name.to_string(),
                    instance_binding.clone(),
                    MatrixSet::new(set, row_len, col_len),
                    s.row_index_name.clone(),
                    row_index_binding,
                    row_bound,
                    s.col_index_name.clone(),
                    col_index_binding,
                    col_bound,
                    value,
                    line_file.clone(),
                )
                .into())
            }
        }
    }

    fn inst_template_proof_process(
        &self,
        proof_process: &[Stmt],
        param_to_arg_map: &HashMap<String, Obj>,
        line_file: &LineFile,
    ) -> Result<Vec<Stmt>, RuntimeError> {
        let mut result = Vec::with_capacity(proof_process.len());
        for proof_stmt in proof_process.iter() {
            result.push(self.inst_template_proof_stmt(proof_stmt, param_to_arg_map, line_file)?);
        }
        Ok(result)
    }

    fn inst_template_proof_stmt(
        &self,
        stmt: &Stmt,
        param_to_arg_map: &HashMap<String, Obj>,
        line_file: &LineFile,
    ) -> Result<Stmt, RuntimeError> {
        match stmt {
            Stmt::Fact(fact) => Ok(self
                .inst_fact(
                    fact,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file.clone()),
                )?
                .into()),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(s)) => {
                let mut facts = Vec::with_capacity(s.facts.len());
                for fact in s.facts.iter() {
                    facts.push(self.inst_fact(
                        fact,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                        Some(line_file.clone()),
                    )?);
                }
                Ok(TrustStmt::new(facts, line_file.clone()).into())
            }
            Stmt::DefObjStmt(DefObjStmt::HaveByExistStmt(s)) => {
                let exist_fact = self.inst_exist_fact(
                    &s.exist_fact_in_have_obj_st,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file),
                )?;
                Ok(HaveByExistStmt::new(
                    s.equal_tos.clone(),
                    s.equal_to_bindings.clone(),
                    exist_fact,
                    line_file.clone(),
                )
                .into())
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(s)) => {
                let mut groups = Vec::with_capacity(s.param_def.groups.len());
                for group in s.param_def.groups.iter() {
                    groups.push(ParamGroupWithParamType::new(
                        group.params.clone(),
                        self.inst_param_type(
                            &group.param_type,
                            param_to_arg_map,
                            ParamObjType::DefHeader,
                        )?,
                    ));
                }
                let mut objs_equal_to = Vec::with_capacity(s.objs_equal_to.len());
                for obj in s.objs_equal_to.iter() {
                    objs_equal_to.push(self.inst_obj(
                        obj,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                    )?);
                }
                Ok(HaveObjEqualStmt::new(
                    ParamDefWithType::new(groups),
                    objs_equal_to,
                    line_file.clone(),
                )
                .into())
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(s)) => {
                let (fn_set_clause, body_map) =
                    self.inst_fn_set_clause(&s.fn_set_clause, param_to_arg_map)?;
                let mut cases = Vec::with_capacity(s.cases.len());
                for case in s.cases.iter() {
                    cases.push(self.inst_and_chain_atomic_fact(
                        case,
                        &body_map,
                        ParamObjType::DefHeader,
                        Some(line_file),
                    )?);
                }
                let mut equal_tos = Vec::with_capacity(s.equal_tos.len());
                for equal_to in s.equal_tos.iter() {
                    equal_tos.push(self.inst_obj(equal_to, &body_map, ParamObjType::DefHeader)?);
                }
                Ok(HaveFnEqualCaseByCaseStmt::new(
                    s.name.clone(),
                    s.symbol_binding.clone(),
                    fn_set_clause,
                    cases,
                    equal_tos,
                    line_file.clone(),
                )
                .into())
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(s)) => {
                let obj = self.inst_obj(
                    &s.equal_to_anonymous_fn.clone().into(),
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let Obj::AnonymousFn(anonymous_fn) = obj else {
                    return Err(RuntimeError::from(InstantiateRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(
                            "local template proof function did not instantiate to anonymous function"
                                .to_string(),
                        ),
                    )));
                };
                Ok(HaveFnEqualStmt::new(
                    s.name.clone(),
                    s.symbol_binding.clone(),
                    anonymous_fn,
                    line_file.clone(),
                )
                .into())
            }
            Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => {
                let mut equal_tos = Vec::with_capacity(s.equal_tos.len());
                for obj in s.equal_tos.iter() {
                    equal_tos.push(self.inst_obj(
                        obj,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                    )?);
                }
                let exist_fact = self.inst_exist_fact(
                    &s.exist_fact_in_witness,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file),
                )?;
                let proof =
                    self.inst_template_proof_process(&s.proof, param_to_arg_map, line_file)?;
                Ok(WitnessExistFact::new(equal_tos, exist_fact, proof, line_file.clone()).into())
            }
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => {
                let obj = self.inst_obj(&s.obj, param_to_arg_map, ParamObjType::DefHeader)?;
                let set = self.inst_obj(&s.set, param_to_arg_map, ParamObjType::DefHeader)?;
                let proof =
                    self.inst_template_proof_process(&s.proof, param_to_arg_map, line_file)?;
                Ok(WitnessNonemptySet::new(obj, set, proof, line_file.clone()).into())
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => {
                let fact = self.inst_fact(
                    &s.fact,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file.clone()),
                )?;
                let proof =
                    self.inst_template_proof_process(&s.proof, param_to_arg_map, line_file)?;
                Ok(ClaimStmt::new(fact, proof, line_file.clone()).into())
            }
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => {
                let proof =
                    self.inst_template_proof_process(&s.proof, param_to_arg_map, line_file)?;
                Ok(SketchStmt::new(proof, line_file.clone()).into())
            }
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) => {
                let proof =
                    self.inst_template_proof_process(&s.proof, param_to_arg_map, line_file)?;
                Ok(TryStmt::new(proof, line_file.clone()).into())
            }
            Stmt::By(ByStmt::ByThmStmt(s)) => {
                let mut args = Vec::with_capacity(s.args.len());
                for arg in s.args.iter() {
                    args.push(self.inst_obj(arg, param_to_arg_map, ParamObjType::DefHeader)?);
                }
                Ok(ByThmStmt::new(s.name.clone(), args, line_file.clone()).into())
            }
            Stmt::By(ByStmt::ByDefStmt(s)) => {
                let fact = self.inst_atomic_fact(
                    &s.fact,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file),
                )?;
                Ok(ByDefStmt::new(fact, line_file.clone()).into())
            }
            Stmt::By(ByStmt::ByCasesStmt(s)) => {
                let mut cases = Vec::with_capacity(s.cases.len());
                for case in s.cases.iter() {
                    cases.push(self.inst_and_chain_atomic_fact(
                        case,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                        Some(line_file),
                    )?);
                }
                let mut then_facts = Vec::with_capacity(s.then_facts.len());
                for fact in s.then_facts.iter() {
                    then_facts.push(self.inst_fact(
                        fact,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                        Some(line_file.clone()),
                    )?);
                }
                let mut proofs = Vec::with_capacity(s.proofs.len());
                for proof in s.proofs.iter() {
                    proofs.push(self.inst_template_proof_process(
                        proof,
                        param_to_arg_map,
                        line_file,
                    )?);
                }
                let mut impossible_facts = Vec::with_capacity(s.impossible_facts.len());
                for impossible_fact in s.impossible_facts.iter() {
                    impossible_facts.push(
                        impossible_fact
                            .as_ref()
                            .map(|fact| {
                                self.inst_atomic_fact(
                                    fact,
                                    param_to_arg_map,
                                    ParamObjType::DefHeader,
                                    Some(line_file),
                                )
                            })
                            .transpose()?,
                    );
                }
                Ok(ByCasesStmt::new(
                    cases,
                    then_facts,
                    proofs,
                    impossible_facts,
                    line_file.clone(),
                )
                .into())
            }
            Stmt::By(ByStmt::ByExtensionStmt(s)) => {
                let left = self.inst_obj(&s.left, param_to_arg_map, ParamObjType::DefHeader)?;
                let right = self.inst_obj(&s.right, param_to_arg_map, ParamObjType::DefHeader)?;
                let proof =
                    self.inst_template_proof_process(&s.proof, param_to_arg_map, line_file)?;
                Ok(ByExtensionStmt::new(left, right, proof, line_file.clone()).into())
            }
            _ => Err(RuntimeError::from(InstantiateRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "template proof body does not support statement `{}` yet",
                    stmt.stmt_type_name()
                )),
            ))),
        }
    }

    fn inst_single_result_param_def(
        &self,
        param_def: &ParamDefWithType,
        param_to_arg_map: &HashMap<String, Obj>,
        instance_binding: &SymbolBinding,
    ) -> Result<ParamDefWithType, RuntimeError> {
        let mut groups = Vec::with_capacity(param_def.groups.len());
        let mut first = true;
        for g in param_def.groups.iter() {
            let mut params = Vec::with_capacity(g.params.len());
            for _ in g.params.iter() {
                if first {
                    params.push(instance_binding.clone());
                    first = false;
                }
            }
            if !params.is_empty() {
                groups.push(ParamGroupWithParamType::new(
                    params,
                    self.inst_param_type(&g.param_type, param_to_arg_map, ParamObjType::DefHeader)?,
                ));
            }
        }
        Ok(ParamDefWithType::new(groups))
    }

    fn inst_fn_set_clause(
        &self,
        clause: &FnSetClause,
        param_to_arg_map: &HashMap<String, Obj>,
    ) -> Result<(FnSetClause, HashMap<String, Obj>), RuntimeError> {
        let mut body_map = param_to_arg_map.clone();
        let mut params_def_with_set = Vec::with_capacity(clause.params_def_with_set.len());
        for g in clause.params_def_with_set.iter() {
            let fresh_group = self.fresh_param_group_with_set(
                g.params
                    .iter()
                    .map(|binding| binding.name().to_string())
                    .collect(),
                self.inst_obj(g.set_obj(), &body_map, ParamObjType::DefHeader)?,
            )?;
            for (source_binding, fresh_binding) in g.params.iter().zip(fresh_group.params.iter()) {
                insert_symbol_substitution(
                    &mut body_map,
                    source_binding,
                    obj_for_bound_param_in_scope(fresh_binding, ParamObjType::FnSet),
                );
            }
            params_def_with_set.push(fresh_group);
        }
        let mut dom_facts = Vec::with_capacity(clause.dom_facts.len());
        for fact in clause.dom_facts.iter() {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(
                fact,
                &body_map,
                ParamObjType::DefHeader,
                None,
            )?);
        }
        let ret_set = self.inst_obj(&clause.ret_set, &body_map, ParamObjType::DefHeader)?;
        Ok((
            FnSetClause::new(params_def_with_set, dom_facts, ret_set)?,
            body_map,
        ))
    }

    fn inst_have_fn_by_induc_case(
        &self,
        c: &HaveFnByInducCase,
        param_to_arg_map: &HashMap<String, Obj>,
        line_file: &LineFile,
    ) -> Result<HaveFnByInducCase, RuntimeError> {
        let case_fact = self.inst_and_chain_atomic_fact(
            &c.case_fact,
            param_to_arg_map,
            ParamObjType::DefHeader,
            Some(line_file),
        )?;
        let body =
            match &c.body {
                HaveFnByInducCaseBody::EqualTo(obj) => HaveFnByInducCaseBody::EqualTo(
                    self.inst_obj(obj, param_to_arg_map, ParamObjType::DefHeader)?,
                ),
                HaveFnByInducCaseBody::NestedCases(cases) => {
                    let mut new_cases = Vec::with_capacity(cases.len());
                    for nested in cases.iter() {
                        new_cases.push(self.inst_have_fn_by_induc_case(
                            nested,
                            param_to_arg_map,
                            line_file,
                        )?);
                    }
                    HaveFnByInducCaseBody::NestedCases(new_cases)
                }
            };
        Ok(HaveFnByInducCase::new(case_fact, body))
    }
}
