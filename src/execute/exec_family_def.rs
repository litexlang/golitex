use crate::prelude::*;

impl Runtime {
    pub fn exec_def_family_stmt(
        &mut self,
        def_family_stmt: &DefFamilyStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let family_definition_infer_result =
            self.run_in_local_env(|rt| rt.def_family_stmt_check_well_defined(def_family_stmt))?;

        self.store_def_family(def_family_stmt)
            .map_err(|store_error| {
                short_exec_error(
                    def_family_stmt.clone().into(),
                    "failed to store family definition",
                    Some(store_error),
                    vec![],
                )
            })?;

        Ok((NonFactualStmtSuccess::new(
            def_family_stmt.clone().into(),
            family_definition_infer_result,
            vec![],
        ))
        .into())
    }

    fn def_family_stmt_check_well_defined(
        &mut self,
        def_family_stmt: &DefFamilyStmt,
    ) -> Result<InferResult, RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        let mut family_definition_infer_result = self
            .define_params_with_type(
                &def_family_stmt.params_def_with_type,
                false,
                ParamObjType::DefHeader,
            )
            .map_err(|define_params_error| {
                short_exec_error(
                    def_family_stmt.clone().into(),
                    "",
                    Some(define_params_error),
                    vec![],
                )
            })?;

        for dom_fact in def_family_stmt.dom_facts.iter() {
            let dom_fact_infer_result = self
                .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    dom_fact,
                    &verify_state,
                )
                .map_err(|inner_exec_error| {
                    short_exec_error(
                        def_family_stmt.clone().into(),
                        "",
                        Some(inner_exec_error),
                        vec![],
                    )
                })?;
            family_definition_infer_result.new_infer_result_inside(dom_fact_infer_result);
        }

        self.verify_obj_well_defined_and_store_cache(&def_family_stmt.equal_to, &verify_state)
            .map_err(|well_defined_error| {
                short_exec_error(
                    def_family_stmt.clone().into(),
                    "",
                    Some(well_defined_error),
                    vec![],
                )
            })?;

        Ok(family_definition_infer_result)
    }
}
