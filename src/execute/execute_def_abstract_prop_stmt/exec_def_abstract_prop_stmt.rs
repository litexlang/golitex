//! `abstract_prop` definition: name + untyped arity, no WD body.
//!
//! Pipeline: ensure name free → store in parent ExecEnv.
//! No local env, no parameter carriers, no iff-facts.

use crate::ast::stmt::DefAbstractPropStmt;
use crate::parse::keywords::{ABSTRACT_PROP, PROP};
use crate::runtime::{Runtime, RuntimeResult};

pub enum ExecDefAbstractPropStmtFailed {
    NameClash(String),
}

/// `abstract_prop name(params)` success payload.
pub struct ExecDefAbstractPropStmtSuccessResult {
    pub statement: DefAbstractPropStmt,
}

pub enum ExecDefAbstractPropStmtResult {
    Success(ExecDefAbstractPropStmtSuccessResult),
    Failed(ExecDefAbstractPropStmtFailed),
}

impl ExecDefAbstractPropStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
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
    ) -> RuntimeResult<ExecDefAbstractPropStmtResult> {
        if let Some(msg) = self.def_abstract_prop_name_clash(&stmt.name) {
            return Ok(ExecDefAbstractPropStmtResult::Failed(
                ExecDefAbstractPropStmtFailed::NameClash(msg),
            ));
        }
        self.top_exec_env_mut()
            .store_def_abstract_prop(stmt.clone());
        Ok(ExecDefAbstractPropStmtResult::Success(
            ExecDefAbstractPropStmtSuccessResult {
                statement: stmt.clone(),
            },
        ))
    }

    fn def_abstract_prop_name_clash(&self, name: &str) -> Option<String> {
        if self.def_abstract_prop_visible_in_stack(name).is_some() {
            return Some(format!(
                "name `{name}` is already used in this scope as {ABSTRACT_PROP}"
            ));
        }
        if self.def_prop_visible_in_stack(name).is_some() {
            return Some(format!(
                "name `{name}` is already used in this scope as {PROP}"
            ));
        }
        None
    }
}
