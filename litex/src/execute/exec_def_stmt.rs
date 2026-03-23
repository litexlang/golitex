use super::Runtime;
use crate::error::ExecStmtError;
use crate::fact::Fact;
use crate::fact::{
    AndChainAtomicFact, AtomicFact, EqualFact, ExistOrAndChainAtomicFact, ForallFact, InFact,
};
use crate::infer::InferResult;
use crate::obj::{Atom, FnObj, Identifier, Obj};
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::stmt::definition_stmt::{
    DefLetStmt, DefPropWithMeaningStmt, DefPropWithoutMeaningStmt, DefStructWithFieldsStmt,
    DefStructWithNoFieldStmt, HaveExistObjStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt,
    HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt,
};
use crate::stmt::parameter_def::{ParamDefWithParamSet, ParamDefWithParamType, ParamType};
use crate::verify::VerifyState;
use std::collections::HashMap;

fn param_defs_with_type_from_fn_set_with_dom(
    fn_set_with_params: &crate::obj::FnSetWithParams,
) -> Vec<ParamDefWithParamType> {
    let mut param_defs_with_type: Vec<ParamDefWithParamType> =
        Vec::with_capacity(fn_set_with_params.params_def_with_set.len());
    for param_def_with_set in fn_set_with_params.params_def_with_set.iter() {
        param_defs_with_type.push(ParamDefWithParamType(
            param_def_with_set.0.clone(),
            ParamType::Obj(param_def_with_set.1.clone()),
        ));
    }
    param_defs_with_type
}

fn build_function_obj_with_param_names(function_name: &str, param_names: &[String]) -> Obj {
    let mut function_args: Vec<Box<Obj>> = Vec::with_capacity(param_names.len());
    for param_name in param_names.iter() {
        function_args.push(Box::new(Obj::Identifier(Identifier::new(
            param_name.clone(),
        ))));
    }
    Obj::FnObj(FnObj::new(
        Atom::IdentifierAtom(Identifier::new(function_name.to_string())),
        vec![function_args],
    ))
}

impl<'a> Runtime<'a> {
    pub fn def_prop_with_meaning_stmt(
        &mut self,
        def_prop_with_meaning_stmt: &DefPropWithMeaningStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.def_prop_with_meaning_stmt_check_well_defined(def_prop_with_meaning_stmt)
            .map_err(|e| {
                ExecStmtError::new(
                    def_prop_with_meaning_stmt.stmt_type_name(),
                    def_prop_with_meaning_stmt.to_string(),
                    Some(e.into()),
                    def_prop_with_meaning_stmt.line_file,
                )
            })?;
        self.store_def_prop_with_meaning(def_prop_with_meaning_stmt)?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                def_prop_with_meaning_stmt.to_string(),
                InferResult::new(),
                vec![],
                def_prop_with_meaning_stmt.line_file,
            ),
        ))
    }

    fn def_prop_with_meaning_stmt_check_well_defined(
        &mut self,
        def_prop_with_meaning_stmt: &DefPropWithMeaningStmt,
    ) -> Result<(), ExecStmtError> {
        self.runtime_context.push_env();

        let result =
            self.def_prop_with_meaning_stmt_check_well_defined_body(def_prop_with_meaning_stmt);

        self.runtime_context.pop_env();
        result
    }

    fn def_prop_with_meaning_stmt_check_well_defined_body(
        &mut self,
        def_prop_with_meaning_stmt: &DefPropWithMeaningStmt,
    ) -> Result<(), ExecStmtError> {
        self.define_params_with_type(&def_prop_with_meaning_stmt.params_def_with_type, false)?;

        for fact in def_prop_with_meaning_stmt.iff_facts.iter() {
            self.verify_fact_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false))?;
        }
        Ok(())
    }

    pub fn def_prop_without_meaning_stmt(
        &mut self,
        def_prop_without_meaning_stmt: &DefPropWithoutMeaningStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.store_def_prop_without_meaning(def_prop_without_meaning_stmt)
            .map_err(|e| {
                ExecStmtError::new(
                    def_prop_without_meaning_stmt.stmt_type_name(),
                    def_prop_without_meaning_stmt.to_string(),
                    Some(e.into()),
                    def_prop_without_meaning_stmt.line_file,
                )
            })?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                def_prop_without_meaning_stmt.to_string(),
                InferResult::new(),
                vec![],
                def_prop_without_meaning_stmt.line_file,
            ),
        ))
    }

    pub fn def_let_stmt(
        &mut self,
        def_let_stmt: &DefLetStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let mut infer_result = self
            .define_params_with_type(&def_let_stmt.param_def, false)
            .map_err(|e| {
                ExecStmtError::new(
                    def_let_stmt.stmt_type_name(),
                    def_let_stmt.to_string(),
                    Some(e.into()),
                    def_let_stmt.line_file,
                )
            })?;
        for fact in def_let_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false))?;
            infer_result.append(fact_infer_result);
        }
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                def_let_stmt.to_string(),
                infer_result,
                vec![],
                def_let_stmt.line_file,
            ),
        ))
    }

    pub fn def_struct_with_fields_stmt(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.store_def_struct_with_fields(def_struct_with_fields_stmt)
            .map_err(|e| {
                ExecStmtError::new(
                    def_struct_with_fields_stmt.stmt_type_name(),
                    def_struct_with_fields_stmt.to_string(),
                    Some(e.into()),
                    def_struct_with_fields_stmt.line_file,
                )
            })?;
        return Err(ExecStmtError::new(
            def_struct_with_fields_stmt.stmt_type_name(),
            "unimplemented".to_string(),
            None,
            def_struct_with_fields_stmt.line_file,
        ));
    }

    pub fn def_struct_with_no_field_stmt(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.store_def_struct_with_no_field(def_struct_with_no_field_stmt)?;
        return Err(ExecStmtError::new(
            def_struct_with_no_field_stmt.stmt_type_name(),
            "unimplemented".to_string(),
            None,
            def_struct_with_no_field_stmt.line_file,
        ));
    }

    pub fn def_algo_stmt(
        &mut self,
        def_algo_stmt: &DefAlgoStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.store_def_algo(def_algo_stmt)?;
        // Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_algo_stmt.to_string(), def_algo_stmt.line_file)))
        return Err(ExecStmtError::new(
            def_algo_stmt.stmt_type_name(),
            "unimplemented".to_string(),
            None,
            def_algo_stmt.line_file,
        ));
    }

    pub fn define_params_with_type(
        &mut self,
        param_defs: &[ParamDefWithParamType],
        check_type_nonempty: bool,
    ) -> Result<InferResult, ExecStmtError> {
        let mut infer_result = InferResult::new();
        for param_def in param_defs.iter() {
            self.verify_param_type_well_defined(&param_def.1, &VerifyState::new(0, false))?;

            self.verify_param_type_nonempty_if_required(&param_def.1, check_type_nonempty)?;

            for name in param_def.0.iter() {
                self.store_identifier_obj(name)?;
                let fact_infer_result = self.store_fact_without_well_defined_verified_and_infer(
                    &ParamType::param_satisfy_param_type_fact(name, &param_def.1),
                )?;
                infer_result.append(fact_infer_result);
            }
        }
        Ok(infer_result)
    }

    pub fn have_obj_in_nonempty_set_or_param_type_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let infer_result = self
            .define_params_with_type(&stmt.param_def, true)
            .map_err(|e| {
                ExecStmtError::new(
                    stmt.stmt_type_name(),
                    stmt.to_string(),
                    Some(e.into()),
                    stmt.line_file,
                )
            })?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(stmt.to_string(), infer_result, vec![], stmt.line_file),
        ))
    }

    pub fn define_params_with_set(
        &mut self,
        param_def: &ParamDefWithParamSet,
    ) -> Result<InferResult, ExecStmtError> {
        self.verify_obj_well_defined_and_store_cache(&param_def.1, &VerifyState::new(0, false))?;
        let mut infer_result = InferResult::new();
        let facts = param_def.facts();
        for (name, fact) in param_def.0.iter().zip(facts.iter()) {
            self.store_identifier_obj(name)?;
            let fact_infer_result =
                self.store_fact_without_well_defined_verified_and_infer(fact)?;
            infer_result.append(fact_infer_result);
        }
        Ok(infer_result)
    }

    pub fn have_obj_equal_stmt(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        if ParamDefWithParamType::number_of_params(&have_obj_equal_stmt.param_def)
            != have_obj_equal_stmt.objs_equal_to.len()
        {
            return Err(ExecStmtError::new( have_obj_equal_stmt.stmt_type_name(),"have_obj_equal_stmt: number of params in param_def does not match number of objs_equal_to".to_string(), None, have_obj_equal_stmt.line_file));
        }

        let mut current_index = 0;
        let mut param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        for param_def in have_obj_equal_stmt.param_def.iter() {
            let current_type = &param_def.1.instantiate(&param_to_obj_map);
            for name in param_def.0.iter() {
                let current_param_equal_to = &have_obj_equal_stmt.objs_equal_to[current_index];

                let fact = ParamType::fact_for_obj(current_param_equal_to.clone(), current_type);
                let verify_result = self
                    .verify_atomic_fact(&fact, &VerifyState::new(0, false))
                    .map_err(ExecStmtError::from)?;
                if !verify_result.is_true() {
                    let msg = format!(
                        "have_obj_equal_stmt: {} is not in type {}",
                        current_param_equal_to, current_type
                    );
                    return Err(ExecStmtError::new(
                        have_obj_equal_stmt.stmt_type_name(),
                        msg,
                        None,
                        have_obj_equal_stmt.line_file,
                    ));
                }

                param_to_obj_map.insert(name.clone(), current_param_equal_to.clone());
                current_index += 1;
            }
        }

        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                have_obj_equal_stmt.to_string(),
                InferResult::new(),
                vec![],
                have_obj_equal_stmt.line_file,
            ),
        ));
    }

    pub fn have_exist_obj_stmt(
        &mut self,
        have_exist_obj_stmt: &HaveExistObjStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let exist_fact_in_have_obj_stmt = &have_exist_obj_stmt.exist_fact_in_have_obj_st;
        let line_file = have_exist_obj_stmt.line_file;
        let verify_state = VerifyState::new(0, false);

        let result = self.verify_exist_fact(exist_fact_in_have_obj_stmt, &verify_state)?;
        if !result.is_true() {
            return Err(ExecStmtError::new(
                have_exist_obj_stmt.stmt_type_name(),
                "have_exist_obj_stmt: exist fact is not verified".to_string(),
                None,
                line_file,
            ));
        }

        if ParamDefWithParamType::number_of_params(
            &exist_fact_in_have_obj_stmt.params_def_with_type,
        ) != have_exist_obj_stmt.equal_tos.len()
        {
            return Err(ExecStmtError::new(
                have_exist_obj_stmt.stmt_type_name(), "have_exist_obj_stmt: number of params in exist does not match number of given objs".to_string(), None,
                line_file,
            ));
        }

        for obj in have_exist_obj_stmt.equal_tos.iter() {
            self.store_identifier_obj(obj)?;
        }

        let new_obj_names_as_identifier_objs = have_exist_obj_stmt
            .equal_tos
            .iter()
            .map(|s| Obj::Identifier(Identifier::new(s.clone())))
            .collect();

        let args_satisfy_param_types =
            ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(
                &exist_fact_in_have_obj_stmt.params_def_with_type,
                &new_obj_names_as_identifier_objs,
            )
            .map_err(|e| {
                ExecStmtError::new(
                    have_exist_obj_stmt.stmt_type_name(),
                    e.error_body(),
                    Some(e),
                    line_file,
                )
            })?;
        let mut infer_result = InferResult::new();
        for fact in args_satisfy_param_types.iter() {
            let fact_infer_result =
                self.store_atomic_fact_without_well_defined_verified_and_infer(fact)?;
            infer_result.append(fact_infer_result);
        }

        let param_to_obj_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &exist_fact_in_have_obj_stmt.params_def_with_type,
            &new_obj_names_as_identifier_objs,
        );

        for fact in exist_fact_in_have_obj_stmt.facts.iter() {
            let instantiated_fact = fact
                .clone()
                .to_exist_or_and_chain_atomic_fact()
                .instantiate(&param_to_obj_map)
                .to_fact();
            let fact_infer_result =
                self.store_fact_without_well_defined_verified_and_infer(&instantiated_fact)?;
            infer_result.append(fact_infer_result);
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                have_exist_obj_stmt.to_string(),
                infer_result,
                vec![],
                have_exist_obj_stmt.line_file,
            ),
        ))
    }

    pub fn have_fn_equal_stmt(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.have_fn_equal_stmt_verify_well_defined(have_fn_equal_stmt)
            .map_err(|e| {
                ExecStmtError::new(
                    have_fn_equal_stmt.stmt_type_name(),
                    "have_fn_equal_stmt: verify well-defined failed".to_string(),
                    Some(e.into()),
                    have_fn_equal_stmt.line_file,
                )
            })?;

        self.store_identifier_obj(&have_fn_equal_stmt.name)?;

        let function_identifier_obj =
            Obj::Identifier(Identifier::new(have_fn_equal_stmt.name.clone()));
        let function_set_obj = Obj::FnSetWithParams(have_fn_equal_stmt.fn_set_with_params.clone());
        let function_in_function_set_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            function_identifier_obj,
            function_set_obj,
            have_fn_equal_stmt.line_file,
        )));
        let mut infer_result = self
            .store_fact_without_well_defined_verified_and_infer(&function_in_function_set_fact)
            .map_err(ExecStmtError::from)?;

        let param_defs_with_type =
            param_defs_with_type_from_fn_set_with_dom(&have_fn_equal_stmt.fn_set_with_params);
        let param_names = ParamDefWithParamSet::collect_param_names(
            &have_fn_equal_stmt.fn_set_with_params.params_def_with_set,
        );
        let function_obj =
            build_function_obj_with_param_names(&have_fn_equal_stmt.name, &param_names);

        let function_equals_equal_to_fact = AtomicFact::EqualFact(EqualFact::new(
            function_obj,
            have_fn_equal_stmt.equal_to.clone(),
            have_fn_equal_stmt.line_file,
        ));
        let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(have_fn_equal_stmt.fn_set_with_params.dom_facts.len());
        for dom_fact in have_fn_equal_stmt.fn_set_with_params.dom_facts.iter() {
            forall_dom_facts.push(dom_fact.clone().to_exist_or_and_chain_atomic_fact());
        }
        let forall_fact = ForallFact::new(
            param_defs_with_type,
            forall_dom_facts,
            vec![crate::fact::ExistOrAndChainAtomicFact::AtomicFact(
                function_equals_equal_to_fact,
            )],
            have_fn_equal_stmt.line_file,
        );
        let forall_as_fact = Fact::ForallFact(forall_fact);
        let forall_infer_result = self
            .store_fact_without_well_defined_verified_and_infer(&forall_as_fact)
            .map_err(ExecStmtError::from)?;
        infer_result.append(forall_infer_result);

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                have_fn_equal_stmt.to_string(),
                infer_result,
                vec![],
                have_fn_equal_stmt.line_file,
            ),
        ))
    }

    fn have_fn_equal_stmt_verify_well_defined(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<(), ExecStmtError> {
        self.runtime_context.push_env();

        let result = self.have_fn_equal_stmt_verify_well_defined_body(have_fn_equal_stmt);

        self.runtime_context.pop_env();
        result
    }

    fn have_fn_equal_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<(), ExecStmtError> {
        let verify_state = VerifyState::new(0, false);

        // 证明 fn_set 是 well-defined 的
        let function_set_obj = Obj::FnSetWithParams(have_fn_equal_stmt.fn_set_with_params.clone());
        self.verify_obj_well_defined_and_store_cache(&function_set_obj, &verify_state)
            .map_err(ExecStmtError::from)?;

        for param_def_with_set in have_fn_equal_stmt
            .fn_set_with_params
            .params_def_with_set
            .iter()
        {
            let _ = self.define_params_with_set(param_def_with_set)?;
        }

        for dom_fact in have_fn_equal_stmt.fn_set_with_params.dom_facts.iter() {
            let _ = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(dom_fact)
                .map_err(ExecStmtError::from)?;
        }

        let equal_to_in_ret_set_atomic_fact = AtomicFact::InFact(InFact::new(
            have_fn_equal_stmt.equal_to.clone(),
            have_fn_equal_stmt
                .fn_set_with_params
                .ret_set
                .as_ref()
                .clone(),
            have_fn_equal_stmt.line_file,
        ));
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(ExecStmtError::from)?;
        if !verify_result.is_true() {
            let msg = format!(
                "have_fn_equal_stmt: {} is not in return set {}",
                have_fn_equal_stmt.equal_to, have_fn_equal_stmt.fn_set_with_params.ret_set
            );
            return Err(ExecStmtError::new(
                have_fn_equal_stmt.stmt_type_name(),
                msg,
                None,
                have_fn_equal_stmt.line_file,
            ));
        }

        Ok(())
    }

    pub fn have_fn_equal_case_by_case_stmt(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.verify_have_fn_equal_case_by_case_stmt(have_fn_equal_case_by_case_stmt)
            .map_err(|e| {
                ExecStmtError::new(
                    have_fn_equal_case_by_case_stmt.stmt_type_name(),
                    "have_fn_equal_case_by_case_stmt: verify well-defined failed".to_string(),
                    Some(e.into()),
                    have_fn_equal_case_by_case_stmt.line_file,
                )
            })?;

        let infer_result =
            self.store_have_fn_equal_case_by_case(have_fn_equal_case_by_case_stmt)?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                have_fn_equal_case_by_case_stmt.to_string(),
                infer_result,
                vec![],
                have_fn_equal_case_by_case_stmt.line_file,
            ),
        ))
    }

    fn store_have_fn_equal_case_by_case(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<InferResult, ExecStmtError> {
        self.store_identifier_obj(&have_fn_equal_case_by_case_stmt.name)?;

        let function_identifier_obj = Obj::Identifier(Identifier::new(
            have_fn_equal_case_by_case_stmt.name.clone(),
        ));
        let function_set_obj =
            Obj::FnSetWithParams(have_fn_equal_case_by_case_stmt.fn_set_with_params.clone());
        let function_in_function_set_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            function_identifier_obj,
            function_set_obj,
            have_fn_equal_case_by_case_stmt.line_file,
        )));

        let mut infer_result = self
            .store_fact_without_well_defined_verified_and_infer(&function_in_function_set_fact)
            .map_err(ExecStmtError::from)?;
        infer_result.push_fact(&function_in_function_set_fact);

        let param_defs_with_type = param_defs_with_type_from_fn_set_with_dom(
            &have_fn_equal_case_by_case_stmt.fn_set_with_params,
        );
        let param_names = ParamDefWithParamSet::collect_param_names(
            &have_fn_equal_case_by_case_stmt
                .fn_set_with_params
                .params_def_with_set,
        );
        let function_obj = build_function_obj_with_param_names(
            &have_fn_equal_case_by_case_stmt.name,
            &param_names,
        );

        for case_index in 0..have_fn_equal_case_by_case_stmt.cases.len() {
            let case_fact = &have_fn_equal_case_by_case_stmt.cases[case_index];
            let equal_to = &have_fn_equal_case_by_case_stmt.equal_tos[case_index];

            let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::with_capacity(
                have_fn_equal_case_by_case_stmt
                    .fn_set_with_params
                    .dom_facts
                    .len()
                    + 1,
            );
            for dom_fact in have_fn_equal_case_by_case_stmt
                .fn_set_with_params
                .dom_facts
                .iter()
            {
                forall_dom_facts.push(dom_fact.clone().to_exist_or_and_chain_atomic_fact());
            }
            forall_dom_facts.push(case_fact.to_exist_or_and_chain_atomic_fact());

            let function_equals_equal_to_fact = AtomicFact::EqualFact(EqualFact::new(
                function_obj.clone(),
                equal_to.clone(),
                have_fn_equal_case_by_case_stmt.line_file,
            ));
            let forall_fact = ForallFact::new(
                param_defs_with_type.clone(),
                forall_dom_facts,
                vec![ExistOrAndChainAtomicFact::AtomicFact(
                    function_equals_equal_to_fact,
                )],
                have_fn_equal_case_by_case_stmt.line_file,
            );
            let forall_as_fact = Fact::ForallFact(forall_fact);

            let forall_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(&forall_as_fact)
                .map_err(ExecStmtError::from)?;
            infer_result.append(forall_infer_result);
            infer_result.push_fact(&forall_as_fact);
        }

        Ok(infer_result)
    }

    fn verify_have_fn_equal_case_by_case_stmt(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<(), ExecStmtError> {
        if have_fn_equal_case_by_case_stmt.cases.len()
            != have_fn_equal_case_by_case_stmt.equal_tos.len()
        {
            return Err(ExecStmtError::new(
                have_fn_equal_case_by_case_stmt.stmt_type_name(),
                "have_fn_equal_case_by_case_stmt: number of cases does not match number of equal_tos".to_string(),
                None,
                have_fn_equal_case_by_case_stmt.line_file,
            ));
        }

        // 证明 fn_set 是 well-defined 的
        let function_set_obj =
            Obj::FnSetWithParams(have_fn_equal_case_by_case_stmt.fn_set_with_params.clone());
        self.verify_obj_well_defined_and_store_cache(
            &function_set_obj,
            &VerifyState::new(0, false),
        )
        .map_err(ExecStmtError::from)?;

        for case_index in 0..have_fn_equal_case_by_case_stmt.cases.len() {
            let case_fact = &have_fn_equal_case_by_case_stmt.cases[case_index];
            let equal_to = &have_fn_equal_case_by_case_stmt.equal_tos[case_index];

            self.runtime_context.push_env();
            let case_result = self
                .have_fn_equal_case_by_case_stmt_verify_well_defined_body_for_one_case(
                    have_fn_equal_case_by_case_stmt,
                    case_fact,
                    equal_to,
                );

            self.runtime_context.pop_env();
            case_result?;
        }

        Ok(())
    }

    fn have_fn_equal_case_by_case_stmt_verify_well_defined_body_for_one_case(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        case_fact: &AndChainAtomicFact,
        equal_to: &Obj,
    ) -> Result<(), ExecStmtError> {
        let verify_state = VerifyState::new(0, false);
        let case_fact_as_fact = case_fact.to_fact();

        for param_def_with_set in have_fn_equal_case_by_case_stmt
            .fn_set_with_params
            .params_def_with_set
            .iter()
        {
            let _ = self.define_params_with_set(param_def_with_set)?;
        }

        for dom_fact in have_fn_equal_case_by_case_stmt
            .fn_set_with_params
            .dom_facts
            .iter()
        {
            let _ = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(dom_fact)
                .map_err(ExecStmtError::from)?;
        }

        let _ = self
            .store_fact_without_well_defined_verified_and_infer(&case_fact_as_fact)
            .map_err(ExecStmtError::from)?;
        self.verify_obj_well_defined_and_store_cache(equal_to, &verify_state)?;

        let equal_to_in_ret_set_atomic_fact = AtomicFact::InFact(InFact::new(
            equal_to.clone(),
            have_fn_equal_case_by_case_stmt
                .fn_set_with_params
                .ret_set
                .as_ref()
                .clone(),
            have_fn_equal_case_by_case_stmt.line_file,
        ));
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(ExecStmtError::from)?;
        if !verify_result.is_true() {
            let msg = format!(
                "have_fn_equal_case_by_case_stmt: {} is not in return set {} under case {}",
                equal_to, have_fn_equal_case_by_case_stmt.fn_set_with_params.ret_set, case_fact,
            );
            return Err(ExecStmtError::new(
                have_fn_equal_case_by_case_stmt.stmt_type_name(),
                msg,
                None,
                have_fn_equal_case_by_case_stmt.line_file,
            ));
        }

        Ok(())
    }
}
