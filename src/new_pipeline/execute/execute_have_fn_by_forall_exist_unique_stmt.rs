//! `have fn name by exist!:` — parse shape-checked; exec not wired in new_pipeline.
//!
//! Parse requires: forall params all Obj (≥1); dom facts quantifier-free; exactly
//! one then which is `exist!`; that `exist!` binds exactly one Obj witness.
//! No proof body under the stmt (prove the forall outside).
//!
//! ```text
//! have fn f by exist!:
//!     ? forall x A:
//!         exist! y B st {$F(x, y)}
//! ```
//!
//! Exec always soft-fails `NotWired` until the EqualToFunction / property
//! design is settled.

use crate::new_pipeline::ast::stmt::HaveFnByForallExistUniqueStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum ExecHaveFnByForallExistUniqueStmtFailed {
    NotWired,
}

pub struct ExecHaveFnByForallExistUniqueStmtSuccessResult {
    pub statement: HaveFnByForallExistUniqueStmt,
}

pub enum ExecHaveFnByForallExistUniqueStmtResult {
    Success(ExecHaveFnByForallExistUniqueStmtSuccessResult),
    Failed(ExecHaveFnByForallExistUniqueStmtFailed),
}

impl ExecHaveFnByForallExistUniqueStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    pub(super) fn exec_have_fn_by_forall_exist_unique_stmt(
        &mut self,
        _stmt: &HaveFnByForallExistUniqueStmt,
    ) -> RuntimeResult<ExecHaveFnByForallExistUniqueStmtResult> {
        Ok(ExecHaveFnByForallExistUniqueStmtResult::Failed(
            ExecHaveFnByForallExistUniqueStmtFailed::NotWired,
        ))
    }
}
