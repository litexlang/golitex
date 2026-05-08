use crate::prelude::*;

impl Runtime {
    pub fn exec_def_struct_stmt(
        &mut self,
        def_struct_stmt: &DefStructStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.def_struct_stmt_check_well_defined(def_struct_stmt))
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_struct_stmt.clone().into(), e))?;
        self.store_def_struct(def_struct_stmt)?;
        Ok(NonFactualStmtSuccess::new_with_stmt(def_struct_stmt.clone().into()).into())
    }

    fn def_struct_stmt_check_well_defined(
        &mut self,
        def_struct_stmt: &DefStructStmt,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);

        if let Some((param_def_with_type, dom_facts)) = &def_struct_stmt.param_def_with_dom {
            self.define_params_with_type(param_def_with_type, false, ParamObjType::DefHeader)?;
            for dom_fact in dom_facts.iter() {
                self.verify_or_and_chain_atomic_fact_well_defined(dom_fact, &verify_state)?;
            }
        }

        for (_, field_type) in def_struct_stmt.fields.iter() {
            self.verify_obj_well_defined_and_store_cache(field_type, &verify_state)?;
        }

        for fact in def_struct_stmt.equivalent_facts.iter() {
            self.verify_fact_well_defined(fact, &verify_state)?;
        }

        Ok(())
    }
}
