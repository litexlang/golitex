use super::exec_stmt_result::{
    DefPropEffect, DefPropWellDefinedResult, ExecDefPropStmtResult,
};
use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // prop name(...): body
    // 1. open local env
    // 2. well-defined in that local env
    // 3. close local env into the result
    // 4. affect global env (store the prop definition)
    pub(super) fn exec_def_prop_stmt(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<ExecDefPropStmtResult> {
        self.ensure_def_prop_name_free(&def_prop.name)?;

        let (well_defined, local_env) = self.run_in_local_env_and_take(|rt| {
            rt.exec_def_prop_stmt_well_defined_in_local(def_prop)
        })?;

        let effect = self.exec_def_prop_stmt_affect_env(def_prop)?;

        Ok(ExecDefPropStmtResult {
            statement: def_prop.clone(),
            well_defined,
            local_env,
            effect,
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

    // Tracer: local phase is opened; full parameter/body WD comes later.
    fn exec_def_prop_stmt_well_defined_in_local(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<DefPropWellDefinedResult> {
        let _ = def_prop;
        let _ = self.top_exec_env();
        Ok(DefPropWellDefinedResult {})
    }

    fn exec_def_prop_stmt_affect_env(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<DefPropEffect> {
        self.top_exec_env_mut().store_def_prop(def_prop.clone());
        Ok(DefPropEffect {
            prop_name: def_prop.name.clone(),
        })
    }
}
