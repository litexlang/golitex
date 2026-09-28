use crate::prelude::*;

impl Runtime {
    pub fn exec_trust_have_stmt(
        &mut self,
        trust_have_stmt: &TrustHaveStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.reject_trust_have_stmt_in_strict_mode(trust_have_stmt)?;
        self.exec_trust_have_stmt_affect_environment_only(trust_have_stmt)
    }

    fn reject_trust_have_stmt_in_strict_mode(
        &mut self,
        trust_have_stmt: &TrustHaveStmt,
    ) -> Result<(), RuntimeError> {
        if self.strict_mode_applies_to_current_module() {
            return Err(short_exec_error(
                trust_have_stmt.clone().into(),
                TrustHaveStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }
        Ok(())
    }

    /// Mathematical contract implementation: `trust have` skips both WD and
    /// truth verification for its bindings and attached facts. The bindings,
    /// facts, and inferred consequences are committed atomically after the
    /// strict-mode gate.
    fn exec_trust_have_stmt_affect_environment(
        &mut self,
        trust_have_stmt: &TrustHaveStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut infer_result = self
            .define_typed_params_with_trust(
                &trust_have_stmt.param_def,
                BindingScope::DefinitionBinding,
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(trust_have_stmt.clone().into(), e))?;
        for fact in trust_have_stmt.facts.iter() {
            let fact_infer_result = self
                .store_fact_with_trust_and_infer_with_reason(fact.clone(), InferReason::TrustHave)
                .map_err(|inner_exec_error| {
                    exec_stmt_error_with_stmt_and_cause(
                        trust_have_stmt.clone().into(),
                        inner_exec_error,
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }

    pub fn exec_trust_have_stmt_affect_environment_only(
        &mut self,
        trust_have_stmt: &TrustHaveStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env_and_commit(|rt| {
            let mut infer_result = rt.exec_trust_have_stmt_affect_environment(trust_have_stmt)?;
            // Parameterized assumptions produce quantified facts in this
            // local environment. Preserve their exact IDs before the scope is
            // popped; a later proposition lookup is not an identity proof.
            rt.attach_known_fact_ids_to_infer_result(&mut infer_result)?;
            Ok(
                SuccessUnsafeStmtResult::TrustHaveStmt(Box::new(SuccessTrustHaveStmtResult {
                    statement: trust_have_stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                }))
                .into(),
            )
        })
    }
}
