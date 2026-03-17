use crate::error::ExecError;
use std::collections::HashMap;
use crate::obj::Obj;
use crate::stmt::parameter_type_and_property::{ParamDefWithParamType, ParamType, ParamDefWithParamSet};
use crate::stmt::definition_stmt::{DefLetStmt, DefPropStmt, DefPropWithoutMeaningStmt, DefStructWithFieldsStmt, DefStructWithNoFieldStmt, HaveObjInNonemptySetOrParamTypeStmt, HaveObjEqualStmt, HaveExistObjStmt, HaveFnEqualStmt, HaveFnEqualCaseByCaseStmt};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn def_prop_stmt(&mut self, def_prop_stmt: &DefPropStmt) -> Result<NonErrStmtExecResult, ExecError> {
        self.def_prop_stmt_check_well_defined(def_prop_stmt)?;
        self.validate_name_and_store_def_prop(def_prop_stmt)?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_prop_stmt.to_string(), def_prop_stmt.line_file_index)))
    }

    fn def_prop_stmt_check_well_defined(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), ExecError> {
        self.runtime_context.new_env();

        let result = self.def_prop_stmt_check_well_defined_body(def_prop_stmt);

        self.runtime_context.delete_env();
        result
    }

    fn def_prop_stmt_check_well_defined_body(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), ExecError> {
        self.define_params_with_type(&def_prop_stmt.params_def_with_type,false)?;

        match &def_prop_stmt.iff_facts {
            None => {},
            Some(iff_facts) => {
                for fact in iff_facts.iter() {
                    self.verify_fact_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false))?;
                }
            }
        }
        Ok(())
    }

    pub fn def_prop_without_meaning_stmt(&mut self, def_prop_without_meaning_stmt: &DefPropWithoutMeaningStmt) -> Result<NonErrStmtExecResult, ExecError> {
        self.validate_name_and_store_def_prop_without_meaning(def_prop_without_meaning_stmt)?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_prop_without_meaning_stmt.to_string(), def_prop_without_meaning_stmt.line_file_index)))
    }

    pub fn def_let_stmt(&mut self, def_let_stmt: &DefLetStmt) -> Result<NonErrStmtExecResult, ExecError> {
        self.define_params_with_type(&def_let_stmt.param_def,false)?;
        for fact in def_let_stmt.facts.iter() {
            self.verify_fact_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false))?;
        }
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_let_stmt.to_string(), def_let_stmt.line_file_index)))
    }

    pub fn def_struct_with_fields_stmt(&mut self, def_struct_with_fields_stmt: &DefStructWithFieldsStmt) -> Result<NonErrStmtExecResult, ExecError> {
        self.validate_name_and_store_def_struct_with_fields(def_struct_with_fields_stmt)?;
        return Err(ExecError::new("def_struct_with_fields_stmt: NOT IMPLEMENTED YET".to_string(), vec![], def_struct_with_fields_stmt.line_file_index));
    }

    pub fn def_struct_with_no_field_stmt(&mut self, def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt) -> Result<NonErrStmtExecResult, ExecError> {
        self.validate_name_and_store_def_struct_with_no_field(def_struct_with_no_field_stmt)?;
        return Err(ExecError::new("def_struct_with_no_field_stmt: NOT IMPLEMENTED YET".to_string(), vec![], def_struct_with_no_field_stmt.line_file_index));
    }

    pub fn def_algo_stmt(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<NonErrStmtExecResult, ExecError> {
        self.validate_name_and_store_def_algo(def_algo_stmt)?;
        // Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_algo_stmt.to_string(), def_algo_stmt.line_file_index)))
        return Err(ExecError::new("def_algo_stmt: NOT IMPLEMENTED YET".to_string(), vec![], def_algo_stmt.line_file_index));
    }

    pub fn define_params_with_type(&mut self, param_defs: &[ParamDefWithParamType], check_type_nonempty: bool) -> Result<(), ExecError> {
        for param_def in param_defs.iter() {
            self.verify_param_type_well_defined(&param_def.1, &VerifyState::new(0, false))?;

            self.verify_param_type_nonempty_if_required(&param_def.1, check_type_nonempty)?;

            for name in param_def.0.iter() {
                self.validate_name_and_store_identifier_obj(name)?;
                self.store_fact_without_well_defined_verified_and_infer(&ParamType::param_satisfy_param_type_fact(name, &param_def.1))?;
            }
        }
        Ok(())
    }

    pub fn have_obj_in_nonempty_set_or_param_type_stmt(&mut self, have_obj_in_nonempty_set_or_param_type_stmt: &HaveObjInNonemptySetOrParamTypeStmt) -> Result<NonErrStmtExecResult, ExecError> {
        self.define_params_with_type(&have_obj_in_nonempty_set_or_param_type_stmt.param_def,true)?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(have_obj_in_nonempty_set_or_param_type_stmt.to_string(), have_obj_in_nonempty_set_or_param_type_stmt.line_file_index)))
    }

    pub fn define_params_with_set(&mut self, param_def: &ParamDefWithParamSet) -> Result<(), ExecError> {
        self.verify_obj_well_defined_and_store_cache(&param_def.1, &VerifyState::new(0, false))?;
        let facts = param_def.facts();
        for (name, fact) in param_def.0.iter().zip(facts.iter()) {
            self.validate_name_and_store_identifier_obj(name)?;
            self.store_fact_without_well_defined_verified_and_infer(fact)?;
        }
        Ok(())
    }

    pub fn have_obj_equal_stmt(&mut self, have_obj_equal_stmt: &HaveObjEqualStmt) -> Result<NonErrStmtExecResult, ExecError> {
        if ParamDefWithParamType::number_of_params(&have_obj_equal_stmt.param_def) != have_obj_equal_stmt.objs_equal_to.len() {
            return Err(ExecError::new("have_obj_equal_stmt: number of params in param_def does not match number of objs_equal_to".to_string(), vec![], have_obj_equal_stmt.line_file_index));
        }

        let mut current_index = 0;
        let mut param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        for param_def in have_obj_equal_stmt.param_def.iter() {
            let current_type = &param_def.1.instantiate(&param_to_obj_map);
            for name in param_def.0.iter() {
                let current_param_equal_to = &have_obj_equal_stmt.objs_equal_to[current_index];

                let fact = ParamType::fact_for_obj(current_param_equal_to.clone(), current_type);
                let verify_result = self.verify_fact(&fact, &VerifyState::new(0, false)).map_err(ExecError::from)?;
                if !verify_result.is_true() {
                    let msg = format!("have_obj_equal_stmt: {} is not in type {}", current_param_equal_to, current_type);
                    return Err(ExecError::new(msg, vec![], have_obj_equal_stmt.line_file_index));
                }

                param_to_obj_map.insert(name.clone(), current_param_equal_to.clone());
                current_index += 1;
            }
        }
        
        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(have_obj_equal_stmt.to_string(), have_obj_equal_stmt.line_file_index)));
    }

    pub fn have_exist_obj_stmt(&mut self, have_exist_obj_stmt: &HaveExistObjStmt) -> Result<NonErrStmtExecResult, ExecError> {
        // 验证 exist 是对的

        // have的obj数量和exist的param对应

        // know have的obj拿去instantiate exist的param后，这些have的obj满足type；然后exist后面的事实全对

        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(have_exist_obj_stmt.to_string(), have_exist_obj_stmt.line_file_index)));
    }

    pub fn have_fn_equal_stmt(&mut self, have_fn_equal_stmt: &HaveFnEqualStmt) -> Result<NonErrStmtExecResult, ExecError> {
        Err(ExecError::new("have_fn_equal_stmt: NOT IMPLEMENTED YET".to_string(), vec![], have_fn_equal_stmt.line_file_index))
    }

    pub fn have_fn_equal_case_by_case_stmt(&mut self, have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt) -> Result<NonErrStmtExecResult, ExecError> {
        Err(ExecError::new("have_fn_equal_case_by_case_stmt: NOT IMPLEMENTED YET".to_string(), vec![], have_fn_equal_case_by_case_stmt.line_file_index))
    }
}
