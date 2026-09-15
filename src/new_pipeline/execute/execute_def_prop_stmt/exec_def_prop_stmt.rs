//! `prop` definition: check WD in a local param scope, then store globally.
//!
//! Pipeline stages (field order matches):
//! 1. param-type WD (inside local env)
//! 2. define typed params into that local env
//! 3. iff-fact WD under those params
//! 4. close local env into the result
//! 5. store the prop definition in the parent ExecEnv

use super::super::exec_stmt_result::StoreHaveObjAndInferResult;
use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, ParamTypeWellDefinedProof, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

/// `prop name(...): body` pipeline result.
///
/// `iff_fact_well_defined` is parallel to `statement.iff_facts`.
/// `local_env` is the closed binder scope (params + any local WD records);
/// it is not merged into the parent. The parent only gains the prop definition.
pub struct ExecDefPropStmtResult {
    pub statement: DefPropStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub defined_params: StoreHaveObjAndInferResult,
    pub iff_fact_well_defined: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

impl Runtime {
    // Mathematical contract: a concrete proposition is checked in a fresh local
    // scope with its typed formal parameters; only the prop definition escapes.
    // Example:
    //   prop is_one(x R):
    //       x = 1
    //   // R WD; x bound locally; x = 1 WD under x; prop stored globally
    pub fn exec_def_prop_stmt(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<ExecDefPropStmtResult> {
        self.ensure_def_prop_name_free(&def_prop.name)?;

        let ((param_type_well_defined, defined_params, iff_fact_well_defined), local_env) =
            self.run_in_local_env_and_take(|rt| rt.exec_def_prop_stmt_in_local(def_prop))?;

        self.top_exec_env_mut().store_def_prop(def_prop.clone());

        Ok(ExecDefPropStmtResult {
            statement: def_prop.clone(),
            param_type_well_defined,
            defined_params,
            iff_fact_well_defined,
            local_env,
        })
    }

    fn ensure_def_prop_name_free(&self, name: &str) -> RuntimeResult<()> {
        let env = self.top_exec_env();
        if env.lookup_def_prop(name).is_some() {
            return Err(RuntimeError::Invariant(format!(
                "name `{name}` is already used in this scope as prop"
            )));
        }
        if env.lookup_def_abstract_prop(name).is_some() {
            return Err(RuntimeError::Invariant(format!(
                "name `{name}` is already used in this scope as abstract_prop"
            )));
        }
        Ok(())
    }

    fn exec_def_prop_stmt_in_local(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<(
        Vec<ParamTypeWellDefinedProof>,
        StoreHaveObjAndInferResult,
        Vec<FactWellDefinedProof>,
    )> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };

        let param_type_well_defined = self.verify_typed_parameters_well_definedness(
            &def_prop.typed_parameters,
            verify_state.clone(),
        )?;
        for proof in &param_type_well_defined {
            if proof.is_unknown() {
                return Err(RuntimeError::Unknown(
                    "prop: unable to establish well-definedness of parameter type".to_string(),
                ));
            }
        }

        let defined_params = self.define_def_prop_params_in_local(def_prop)?;

        let mut iff_fact_well_defined = Vec::with_capacity(def_prop.iff_facts.len());
        for fact in &def_prop.iff_facts {
            let wd = self.verify_fact_well_definedness(fact, verify_state.clone())?;
            if wd.is_unknown() {
                return Err(RuntimeError::Unknown(
                    "prop: unable to establish well-definedness of iff fact".to_string(),
                ));
            }
            iff_fact_well_defined.push(wd);
        }

        Ok((
            param_type_well_defined,
            defined_params,
            iff_fact_well_defined,
        ))
    }

    fn define_def_prop_params_in_local(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<StoreHaveObjAndInferResult> {
        let mut stored_fact_ids = Vec::new();
        for group in &def_prop.typed_parameters.groups {
            for identifier in &group.params {
                if self
                    .top_exec_env()
                    .definitions
                    .identifiers
                    .contains_key(&identifier.name)
                {
                    return Err(RuntimeError::Invariant(format!(
                        "identifier `{}` is already defined in this ExecEnv",
                        identifier.name
                    )));
                }
                self.top_exec_env_mut().definitions.identifiers.insert(
                    identifier.name.clone(),
                    DefinedIdentifierInfo {
                        identifier: identifier.clone(),
                    },
                );
                // Type facts belong in KnownFactMemory once that store is wired.
                stored_fact_ids.push(self.ids.allocate_fact_id());
            }
        }
        Ok(StoreHaveObjAndInferResult { stored_fact_ids })
    }
}
