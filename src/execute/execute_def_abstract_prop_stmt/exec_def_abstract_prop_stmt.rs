//! `abstract_prop` definition: name + untyped arity, no WD body.
//!
//! Pipeline: ensure name free → store in parent ExecEnv.
//! No local env, no parameter carriers, no iff-facts.

use crate::ast::stmt::DefAbstractPropStmt;
use crate::parse::keywords::{ABSTRACT_PROP, PROP};
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};

/// `abstract_prop name(params)` success payload (no soft-fail path yet).
pub struct ExecDefAbstractPropStmtSuccessResult {
    pub statement: DefAbstractPropStmt,
}

impl Runtime {
    // Mathematical contract: an abstract_prop header is only an uninterpreted
    // predicate name and untyped formal argument names; it introduces no
    // object-domain WD obligation. Example:
    //   abstract_prop prime(n)
    //   // stores the interface; $prime(17) stays unknown until assumed/proved
    pub(in crate::execute) fn exec_def_abstract_prop_stmt(
        &mut self,
        stmt: &DefAbstractPropStmt,
    ) -> RuntimeResult<ExecDefAbstractPropStmtSuccessResult> {
        self.ensure_def_abstract_prop_name_free(&stmt.name)?;
        self.top_exec_env_mut()
            .store_def_abstract_prop(stmt.clone());
        Ok(ExecDefAbstractPropStmtSuccessResult {
            statement: stmt.clone(),
        })
    }

    fn ensure_def_abstract_prop_name_free(&self, name: &str) -> RuntimeResult<()> {
        if self.def_abstract_prop_visible_in_stack(name).is_some() {
            return Err(RuntimeError::InternalBug(format!(
                "name `{name}` is already used in this scope as {ABSTRACT_PROP}"
            )));
        }
        if self.def_prop_visible_in_stack(name).is_some() {
            return Err(RuntimeError::InternalBug(format!(
                "name `{name}` is already used in this scope as {PROP}"
            )));
        }
        Ok(())
    }
}
