use crate::prelude::*;

impl Runtime {
    pub fn exec_let_stmt(&mut self, def_let_stmt: &DefLetStmt) -> Result<StmtResult, RuntimeError> {
        if self.strict_mode {
            return Err(short_exec_error(
                def_let_stmt.clone().into(),
                "strict mode rejects user let statements; use have/claim/thm/prove or move trusted background into an imported module",
                None,
                vec![],
            ));
        }

        let mut infer_result = self
            .define_params_with_type(&def_let_stmt.param_def, false, ParamObjType::Identifier)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_let_stmt.clone().into(), e))?;
        for fact in def_let_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer_with_reason(
                    fact.clone(),
                    &VerifyState::new(0, false),
                    InferReason::LetBinding,
                )
                .map_err(|inner_exec_error| {
                    exec_stmt_error_with_stmt_and_cause(
                        def_let_stmt.clone().into(),
                        inner_exec_error,
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok((NonFactualStmtSuccess::new(def_let_stmt.clone().into(), infer_result, vec![])).into())
    }
}
