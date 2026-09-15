//! `prop` definition: check WD in a local param scope, then store globally.
//!
//! Pipeline stages (field order matches):
//! 1–2. introduce typed params in local env (param-type WD + define)
//! 3. iff-fact WD under those params
//! 4. close local env into the result
//! 5. store the prop definition in the parent ExecEnv

use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, ParamTypeWellDefinedProof, VerifyFactResult, VerifyObjWellDefinedResult,
    VerifyState,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::new_pipeline::execute::IntroduceTypedParametersResult;
use crate::new_pipeline::parse::keywords::{ABSTRACT_PROP, PROP};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

pub enum ExecDefPropStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    IffFactWellDefined(VerifyFactResult),
}

/// `prop name(...): body` pipeline success payload.
///
/// `iff_fact_well_defined` is parallel to `statement.iff_facts`.
/// `local_env` is the closed binder scope (params + any local WD records);
/// it is not merged into the parent. The parent only gains the prop definition.
pub struct ExecDefPropStmtSuccessResult {
    pub statement: DefPropStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub defined_params: StoreHaveObjAndInferResult,
    pub iff_fact_well_defined: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecDefPropStmtResult {
    Success(ExecDefPropStmtSuccessResult),
    Failed(ExecDefPropStmtFailed),
}

impl ExecDefPropStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Mathematical contract: a concrete proposition is checked in a fresh local
    // scope with its typed formal parameters; only the prop definition escapes.
    // Example:
    //   prop is_one(x R):
    //       x = 1
    //   // R WD; x bound locally; x = 1 WD under x; prop stored globally
    pub(in crate::new_pipeline::execute) fn exec_def_prop_stmt(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<ExecDefPropStmtResult> {
        self.ensure_def_prop_name_free(&def_prop.name)?;

        let (local_outcome, local_env) =
            self.run_in_local_env_and_take_env(|rt| rt.exec_def_prop_stmt_in_local(def_prop))?;

        let (introduced, iff_fact_well_defined) = match local_outcome {
            Ok(parts) => parts,
            Err(failed) => return Ok(ExecDefPropStmtResult::Failed(failed)),
        };

        self.top_exec_env_mut().store_def_prop(def_prop.clone());

        Ok(ExecDefPropStmtResult::Success(ExecDefPropStmtSuccessResult {
            statement: def_prop.clone(),
            param_type_well_defined: introduced.param_type_well_defined,
            defined_params: introduced.defined_params,
            iff_fact_well_defined,
            local_env,
        }))
    }

    fn ensure_def_prop_name_free(&self, name: &str) -> RuntimeResult<()> {
        if self.def_prop_visible_in_stack(name).is_some() {
            return Err(RuntimeError::Invariant(format!(
                "name `{name}` is already used in this scope as {PROP}"
            )));
        }
        if self.def_abstract_prop_visible_in_stack(name).is_some() {
            return Err(RuntimeError::Invariant(format!(
                "name `{name}` is already used in this scope as {ABSTRACT_PROP}"
            )));
        }
        Ok(())
    }

    fn exec_def_prop_stmt_in_local(
        &mut self,
        def_prop: &DefPropStmt,
    ) -> RuntimeResult<
        Result<(IntroduceTypedParametersResult, Vec<FactWellDefinedProof>), ExecDefPropStmtFailed>,
    > {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };

        let introduced = match self
            .introduce_typed_parameters(&def_prop.typed_parameters, verify_state.clone())?
        {
            Ok(result) => result,
            Err(failed) => return Ok(Err(ExecDefPropStmtFailed::ParamType(failed))),
        };

        let mut iff_fact_well_defined = Vec::with_capacity(def_prop.iff_facts.len());
        for fact in &def_prop.iff_facts {
            let wd = self.verify_fact_well_definedness(fact, verify_state.clone())?;
            if wd.is_failed() {
                return Ok(Err(ExecDefPropStmtFailed::IffFactWellDefined(
                    VerifyFactResult::FailToVerifyWellDefined,
                )));
            }
            iff_fact_well_defined.push(wd);
        }

        Ok(Ok((introduced, iff_fact_well_defined)))
    }
}
