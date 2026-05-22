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
        let verify_state = VerifyState::new(0, false);
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
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let def = self
            .get_template_definition_by_name(&template_obj.template_name)
            .cloned()
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "template `{}` is not defined",
                        template_obj.template_name
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

        let instance_name = template_obj.to_string();
        let stmt = self.inst_template_body_stmt(
            &def.template_def_stmt,
            &param_to_arg_map,
            &instance_name,
            &def.line_file,
        )?;
        self.exec_stmt(&stmt)?;
        Ok(())
    }

    fn inst_template_body_stmt(
        &self,
        stmt: &TemplateDefEnum,
        param_to_arg_map: &HashMap<String, Obj>,
        instance_name: &str,
        line_file: &LineFile,
    ) -> Result<Stmt, RuntimeError> {
        match stmt {
            TemplateDefEnum::HaveObjInNonemptySetStmt(s) => {
                let param_def = self.inst_single_result_param_def(
                    &s.param_def,
                    param_to_arg_map,
                    instance_name,
                )?;
                Ok(HaveObjInNonemptySetOrParamTypeStmt::new(param_def, line_file.clone()).into())
            }
            TemplateDefEnum::HaveObjEqualStmt(s) => {
                let param_def = self.inst_single_result_param_def(
                    &s.param_def,
                    param_to_arg_map,
                    instance_name,
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
            TemplateDefEnum::HaveByExistStmt(s) => {
                let exist_fact = self.inst_exist_fact(
                    &s.exist_fact_in_have_obj_st,
                    param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(line_file),
                )?;
                Ok(HaveByExistStmt::new(
                    vec![instance_name.to_string()],
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
                Ok(
                    HaveFnEqualStmt::new(
                        instance_name.to_string(),
                        anonymous_fn,
                        line_file.clone(),
                    )
                    .into(),
                )
            }
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(s) => {
                let fn_set_clause = self.inst_fn_set_clause(&s.fn_set_clause, param_to_arg_map)?;
                let mut cases = Vec::with_capacity(s.cases.len());
                for c in s.cases.iter() {
                    cases.push(self.inst_and_chain_atomic_fact(
                        c,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                        Some(line_file),
                    )?);
                }
                let mut equal_tos = Vec::with_capacity(s.equal_tos.len());
                for obj in s.equal_tos.iter() {
                    equal_tos.push(self.inst_obj(
                        obj,
                        param_to_arg_map,
                        ParamObjType::DefHeader,
                    )?);
                }
                Ok(HaveFnEqualCaseByCaseStmt::new(
                    instance_name.to_string(),
                    fn_set_clause,
                    cases,
                    equal_tos,
                    line_file.clone(),
                )
                .into())
            }
            TemplateDefEnum::HaveFnByInducStmt(s) => {
                let fn_set_clause = self.inst_fn_set_clause(&s.fn_set_clause, param_to_arg_map)?;
                let measure =
                    self.inst_obj(&s.measure, param_to_arg_map, ParamObjType::DefHeader)?;
                let lower_bound =
                    self.inst_obj(&s.lower_bound, param_to_arg_map, ParamObjType::DefHeader)?;
                let mut cases = Vec::with_capacity(s.cases.len());
                for c in s.cases.iter() {
                    cases.push(self.inst_have_fn_by_induc_case(c, param_to_arg_map, line_file)?);
                }
                Ok(HaveFnByInducStmt::new(
                    instance_name.to_string(),
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
                Ok(HaveFnByForallExistUniqueStmt::new(
                    instance_name.to_string(),
                    forall,
                    line_file.clone(),
                )
                .into())
            }
        }
    }

    fn inst_single_result_param_def(
        &self,
        param_def: &ParamDefWithType,
        param_to_arg_map: &HashMap<String, Obj>,
        instance_name: &str,
    ) -> Result<ParamDefWithType, RuntimeError> {
        let mut groups = Vec::with_capacity(param_def.groups.len());
        let mut first = true;
        for g in param_def.groups.iter() {
            let mut params = Vec::with_capacity(g.params.len());
            for _ in g.params.iter() {
                if first {
                    params.push(instance_name.to_string());
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
    ) -> Result<FnSetClause, RuntimeError> {
        let mut params_def_with_set = Vec::with_capacity(clause.params_def_with_set.len());
        for g in clause.params_def_with_set.iter() {
            params_def_with_set.push(ParamGroupWithSet::new(
                g.params.clone(),
                self.inst_obj(g.set_obj(), param_to_arg_map, ParamObjType::DefHeader)?,
            ));
        }
        let mut dom_facts = Vec::with_capacity(clause.dom_facts.len());
        for fact in clause.dom_facts.iter() {
            dom_facts.push(self.inst_or_and_chain_atomic_fact(
                fact,
                param_to_arg_map,
                ParamObjType::DefHeader,
                None,
            )?);
        }
        let ret_set = self.inst_obj(&clause.ret_set, param_to_arg_map, ParamObjType::DefHeader)?;
        FnSetClause::new(params_def_with_set, dom_facts, ret_set)
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
