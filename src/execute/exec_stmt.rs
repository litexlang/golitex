//! Tier 1 frozen backbone: transactional statement boundary and `-strict` gate.
//! Statement-variant dispatch lives in Tier 2 `dispatch_stmt.rs`.

use super::exec_stmt_result::ExecStmtResult;
use crate::ast::stmt::{DefinitionStmt, Stmt, TemplateDefEnum};
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // Temp ExecEnv → run stmt → Failed discards child; Success merges into parent.
    // Soft-fail must not pollute the parent session (see exec_env/merge_exec_env.rs).
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        let (outcome, child_env) =
            self.run_in_local_env_and_take_env(|runtime| runtime.exec_stmt_in_current_env(stmt))?;

        if outcome.is_failed() {
            return Ok(outcome.retain_failed_statement_scope(child_env));
        }
        self.top_exec_env_mut().merge_from(&child_env)?;
        Ok(outcome)
    }

    fn exec_stmt_in_current_env(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        if self.launch_command.is_strict() {
            let forbidden_assumption = match stmt {
                Stmt::Trust(_) => Some("`trust` / `trust have` are forbidden"),
                Stmt::Definition(DefinitionStmt::AxiomStmt(_)) => Some("`axiom` is forbidden"),
                Stmt::Definition(DefinitionStmt::DefTemplateStmt(template))
                    if matches!(
                        &template.template_def_stmt,
                        TemplateDefEnum::TrustHaveStmt(_)
                    ) =>
                {
                    Some("`trust` / `trust have` are forbidden")
                }
                _ => None,
            };
            if let Some(forbidden_assumption) = forbidden_assumption {
                return Err(RuntimeError::InvalidArguments(format!(
                    "{} under {} `-strict`",
                    forbidden_assumption,
                    crate::LITEX
                )));
            }
        }
        self.dispatch_stmt_in_current_env(stmt)
    }
}
