use crate::error::ExecError;
use crate::stmt::parameter_type_and_property::{ParamDefWithParamType};
use crate::stmt::definition_stmt::{DefLetStmt, DefPropStmt, DefStmt, DefStructStmt, HaveObjInNonemptySetOrParamTypeStmt, HaveObjEqualStmt, HaveExistObjStmt, HaveFnEqualStmt, HaveFnEqualCaseByCaseStmt};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::result::StmtResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn def_stmt(&mut self, def_stmt: &DefStmt) -> Result<StmtResult, ExecError> {
        match def_stmt {
            DefStmt::DefPropStmt(def_prop_stmt) => self.def_prop_stmt(def_prop_stmt),
            DefStmt::DefLetStmt(def_let_stmt) => self.def_let_stmt(def_let_stmt),
            DefStmt::DefStructStmt(def_struct_stmt) => self.def_struct_stmt(def_struct_stmt),
            DefStmt::DefAlgoStmt(def_algo_stmt) => self.def_algo_stmt(def_algo_stmt),
            DefStmt::HaveObjInNonemptySetStmt(have_obj_in_nonempty_set_stmt) => self.have_obj_in_nonempty_set_or_param_type_stmt(have_obj_in_nonempty_set_stmt),
            DefStmt::HaveObjEqualStmt(have_obj_equal_stmt) => self.have_obj_equal_stmt(have_obj_equal_stmt),
            DefStmt::HaveExistObjStmt(have_exist_obj_stmt) => self.have_exist_obj_stmt(have_exist_obj_stmt),
            DefStmt::HaveFnEqualStmt(have_fn_equal_stmt) => self.have_fn_equal_stmt(have_fn_equal_stmt),
            DefStmt::HaveFnEqualCaseByCaseStmt(have_fn_equal_case_by_case_stmt) => self.have_fn_equal_case_by_case_stmt(have_fn_equal_case_by_case_stmt),
        }
    }

    fn def_prop_stmt(&mut self, def_prop_stmt: &DefPropStmt) -> Result<StmtResult, ExecError> {
        self.def_prop_stmt_check_well_defined(def_prop_stmt)?;
        self.validate_name_and_store_def_prop(def_prop_stmt)?;
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_prop_stmt.to_string(), def_prop_stmt.line_file_index)))
    }

    fn def_prop_stmt_check_well_defined(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), ExecError> {
        self.runtime_context.new_env();
        let result = self.def_prop_stmt_check_well_defined_body(def_prop_stmt);
        self.runtime_context.delete_env();
        result
    }

    fn def_prop_stmt_check_well_defined_body(&mut self, def_prop_stmt: &DefPropStmt) -> Result<(), ExecError> {
        match &def_prop_stmt.iff_facts {
            None => {},
            Some(iff_facts) => {
                for fact in iff_facts.iter() {
                    self.verify_fact_well_defined(fact, &mut VerifyState::new(0, false))?;
                }
            }
        }
        Ok(())
    }

    fn def_let_stmt(&mut self, def_let_stmt: &DefLetStmt) -> Result<StmtResult, ExecError> {
        for param_def in def_let_stmt.param_def.iter() {
            self.define_params_with_type(param_def)?;
        }
        for fact in def_let_stmt.facts.iter() {
            self.store_fact(fact)?;
        }
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_let_stmt.to_string(), def_let_stmt.line_file_index)))
    }

    fn def_struct_stmt(&mut self, def_struct_stmt: &DefStructStmt) -> Result<StmtResult, ExecError> {
        self.validate_name_and_store_def_struct(def_struct_stmt)?;
        // Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_struct_stmt.to_string(), def_struct_stmt.line_file_index())))
        return Err(ExecError::new("def_struct_stmt: NOT IMPLEMENTED YET", vec![], def_struct_stmt.line_file_index()));
    }

    fn def_algo_stmt(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<StmtResult, ExecError> {
        self.validate_name_and_store_def_algo(def_algo_stmt)?;
        // Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_algo_stmt.to_string(), def_algo_stmt.line_file_index)))
        return Err(ExecError::new("def_algo_stmt: NOT IMPLEMENTED YET", vec![], def_algo_stmt.line_file_index));
    }

    fn have_obj_in_nonempty_set_or_param_type_stmt(&mut self, have_obj_in_nonempty_set_or_param_type_stmt: &HaveObjInNonemptySetOrParamTypeStmt) -> Result<StmtResult, ExecError> {
        return Err(ExecError::new("have_obj_in_nonempty_set_or_param_type_stmt: NOT IMPLEMENTED YET", vec![], have_obj_in_nonempty_set_or_param_type_stmt.line_file_index));
    }

    fn have_obj_equal_stmt(&mut self, have_obj_equal_stmt: &HaveObjEqualStmt) -> Result<StmtResult, ExecError> {
        return Err(ExecError::new("have_obj_equal_stmt: NOT IMPLEMENTED YET", vec![], have_obj_equal_stmt.line_file_index));
    }

    fn have_exist_obj_stmt(&mut self, have_exist_obj_stmt: &HaveExistObjStmt) -> Result<StmtResult, ExecError> {
        return Err(ExecError::new("have_exist_obj_stmt: NOT IMPLEMENTED YET", vec![], have_exist_obj_stmt.line_file_index));
    }

    fn have_fn_equal_stmt(&mut self, have_fn_equal_stmt: &HaveFnEqualStmt) -> Result<StmtResult, ExecError> {
        return Err(ExecError::new("have_fn_equal_stmt: NOT IMPLEMENTED YET", vec![], have_fn_equal_stmt.line_file_index));
    }

    fn have_fn_equal_case_by_case_stmt(&mut self, have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt) -> Result<StmtResult, ExecError> {
        return Err(ExecError::new("have_fn_equal_case_by_case_stmt: NOT IMPLEMENTED YET", vec![], have_fn_equal_case_by_case_stmt.line_file_index));
    }

    /// 为 ParamDefWithParamType（let 等用的参数类型）校验名字并写入参数对应的 facts。
    fn define_params_with_type(&mut self, param_def: &ParamDefWithParamType) -> Result<(), ExecError> {
        let facts = param_def.facts();
        for (name, fact) in param_def.0.iter().zip(facts.iter()) {
            self.validate_name_and_store_identifier_obj(name)?;
            self.store_fact(fact)?;
        }
        Ok(())
    }

}
