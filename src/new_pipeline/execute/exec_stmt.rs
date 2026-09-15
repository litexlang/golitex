use super::exec_stmt_result::{
    ExecDefinitionStmtFailed, ExecDefinitionStmtSuccess, ExecStmtFailed, ExecStmtResult,
    ExecStmtSuccess,
};
use crate::new_pipeline::ast::stmt::{DefinitionStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // Only public stmt entry: temp ExecEnv → exec_xxx → Failed | merge+Success.
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        let (outcome, child_env) =
            self.run_in_local_env_and_take_env(|runtime| runtime.exec_stmt_in_current_env(stmt))?;

        match outcome {
            ExecStmtResult::Failed(failed) => Ok(ExecStmtResult::Failed(failed)),
            ExecStmtResult::Success(success) => {
                self.top_exec_env_mut().merge_from(&child_env)?;
                Ok(ExecStmtResult::Success(success))
            }
        }
    }

    // Runs with the current top as the writable work env (the temp shell).
    fn exec_stmt_in_current_env(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        match stmt {
            Stmt::Fact(fact) => match self.execute_fact_statement(fact)? {
                Ok(result) => Ok(ExecStmtResult::Success(ExecStmtSuccess::Fact(result))),
                Err(verify_result) => Ok(ExecStmtResult::Failed(ExecStmtFailed::Fact(verify_result))),
            },
            Stmt::Definition(DefinitionStmt::LetObjStmt(let_stmt)) => {
                match self.exec_let_obj(let_stmt)? {
                    Ok(result) => Ok(ExecStmtResult::Success(ExecStmtSuccess::Definition(
                        ExecDefinitionStmtSuccess::LetObj(result),
                    ))),
                    Err(wd) => Ok(ExecStmtResult::Failed(ExecStmtFailed::Definition(
                        ExecDefinitionStmtFailed::LetObj(wd),
                    ))),
                }
            }
            Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(have_stmt)) => {
                match self.exec_have_obj_in_nonempty_set_stmt(have_stmt)? {
                    Ok(result) => Ok(ExecStmtResult::Success(ExecStmtSuccess::Definition(
                        ExecDefinitionStmtSuccess::HaveObjInNonemptySet(result),
                    ))),
                    Err(failed) => Ok(ExecStmtResult::Failed(ExecStmtFailed::Definition(
                        ExecDefinitionStmtFailed::HaveObjInNonemptySet(failed),
                    ))),
                }
            }
            Stmt::Definition(DefinitionStmt::DefPropStmt(def_prop)) => {
                match self.exec_def_prop_stmt(def_prop)? {
                    Ok(result) => Ok(ExecStmtResult::Success(ExecStmtSuccess::Definition(
                        ExecDefinitionStmtSuccess::DefProp(result),
                    ))),
                    Err(failed) => Ok(ExecStmtResult::Failed(ExecStmtFailed::Definition(
                        ExecDefinitionStmtFailed::DefProp(failed),
                    ))),
                }
            }
            Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(def_abstract_prop)) => {
                Ok(ExecStmtResult::Success(ExecStmtSuccess::Definition(
                    ExecDefinitionStmtSuccess::DefAbstractProp(
                        self.exec_def_abstract_prop_stmt(def_abstract_prop)?,
                    ),
                )))
            }
            Stmt::UnsafeStmt(unsafe_stmt) => match self.exec_unsafe_stmt(unsafe_stmt)? {
                Ok(result) => Ok(ExecStmtResult::Success(ExecStmtSuccess::Unsafe(result))),
                Err(failed) => Ok(ExecStmtResult::Failed(ExecStmtFailed::Unsafe(failed))),
            },
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_stmt: only Fact, let, have-obj-in-nonempty, prop, abstract_prop, and trust are wired for the tracer"
                    .to_string(),
            )),
        }
    }
}
