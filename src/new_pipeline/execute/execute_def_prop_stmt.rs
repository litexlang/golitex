use super::exec_stmt_result::ExecDefPropStmtResult;
use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, ParamTypeWellDefinedProof, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // prop name(...): body
    // 1. open local env
    // 2. well-defined in that local env (param types, then iff-facts)
    // 3. close local env into the result
    // 4. affect global env (store the prop definition)
    pub(super) fn exec_def_prop_stmt(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<ExecDefPropStmtResult> {
        self.ensure_def_prop_name_free(&def_prop.name)?;

        let ((param_type_well_defined, iff_fact_well_defined), local_env) =
            self.run_in_local_env_and_take(|rt| {
                rt.exec_def_prop_stmt_well_defined_in_local(def_prop)
            })?;

        self.top_exec_env_mut().store_def_prop(def_prop.clone());

        Ok(ExecDefPropStmtResult {
            statement: def_prop.clone(),
            param_type_well_defined,
            iff_fact_well_defined,
            local_env,
            prop_name: def_prop.name.clone(),
        })
    }

    fn ensure_def_prop_name_free(&self, name: &str) -> RuntimeResult<()> {
        let env = self.top_exec_env();
        if env.lookup_def_prop(name).is_some() {
            return Err(RuntimeError::Invariant(format!(
                "name `{name}` is already used in this scope as prop"
            )));
        }
        if env
            .definitions
            .abstract_predicate_definitions
            .contains_key(name)
        {
            return Err(RuntimeError::Invariant(format!(
                "name `{name}` is already used in this scope as abstract_prop"
            )));
        }
        Ok(())
    }

    fn exec_def_prop_stmt_well_defined_in_local(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<(Vec<ParamTypeWellDefinedProof>, Vec<FactWellDefinedProof>)> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };

        let param_type_well_defined = self.verify_typed_parameters_well_definedness(
            &def_prop.typed_parameters,
            verify_state.clone(),
        )?;

        let mut iff_fact_well_defined = Vec::new();
        for fact in &def_prop.iff_facts {
            iff_fact_well_defined
                .push(self.verify_fact_well_definedness(fact, verify_state.clone())?);
        }

        Ok((param_type_well_defined, iff_fact_well_defined))
    }
}
