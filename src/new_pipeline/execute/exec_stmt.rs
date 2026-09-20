use super::exec_stmt_result::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::new_pipeline::ast::stmt::{ByStmt, DefinitionStmt, Stmt};
use crate::new_pipeline::execute::execute_by_stmt::{
    exec_by_cases_stmt, exec_by_contra_stmt, exec_by_def_stmt, exec_by_induc_stmt,
    exec_by_extension_stmt, exec_by_enumerate_finite_set_stmt, exec_by_for_stmt,
    exec_by_enumerate_range_stmt, exec_by_closed_range_as_cases_stmt, exec_by_reflexive_prop_stmt, exec_by_strong_induc_stmt,
    exec_by_symmetric_prop_stmt, exec_by_thm_stmt, exec_by_transitive_prop_stmt,
    exec_release_thm_stmt,
};
use crate::new_pipeline::execute::execute_def_thm_stmt::exec_def_thm_stmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // Temp ExecEnv → run stmt → Failed discards child; Success merges into parent.
    // Soft-fail must not pollute the parent session (see exec_env/merge_exec_env.rs).
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        let (outcome, child_env) =
            self.run_in_local_env_and_take_env(|runtime| runtime.exec_stmt_in_current_env(stmt))?;

        if outcome.is_failed() {
            return Ok(outcome);
        }
        self.top_exec_env_mut().merge_from(&child_env)?;
        Ok(outcome)
    }

    fn exec_stmt_in_current_env(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        if self.launch_command.is_strict() {
            match stmt {
                Stmt::UnsafeStmt(_) => {
                    return Err(RuntimeError::InvalidArguments(format!(
                        "`trust` / `trust have` are forbidden under {} `-strict`",
                        crate::new_pipeline::LITEX
                    )));
                }
                Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(_)) => {
                    return Err(RuntimeError::InvalidArguments(format!(
                        "`abstract_prop` is forbidden under {} `-strict`",
                        crate::new_pipeline::LITEX
                    )));
                }
                _ => {}
            }
        }
        match stmt {
            Stmt::Fact(fact) => Ok(ExecStmtResult::Fact(self.execute_fact_statement(fact)?)),
            Stmt::Definition(DefinitionStmt::LetObjStmt(let_stmt)) => Ok(ExecStmtResult::Definition(
                ExecDefinitionStmtResult::LetObj(self.exec_let_obj(let_stmt)?),
            )),
            Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(have_stmt)) => {
                Ok(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveObjInNonemptySet(
                        self.exec_have_obj_in_nonempty_set_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(have_stmt)) => {
                Ok(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveObjEqual(
                        self.exec_have_obj_equal_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(have_stmt)) => {
                Ok(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveObjByExistFacts(
                        self.exec_have_obj_by_exist_facts_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(have_stmt)) => {
                Ok(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::HaveFnEqual(
                        self.exec_have_fn_equal_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Definition(DefinitionStmt::DefPropStmt(def_prop)) => {
                Ok(ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
                    self.exec_def_prop_stmt(def_prop)?,
                )))
            }
            Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(def_abstract_prop)) => {
                Ok(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::DefAbstractProp(
                        self.exec_def_abstract_prop_stmt(def_abstract_prop)?,
                    ),
                ))
            }
            Stmt::Definition(DefinitionStmt::DefStructStmt(def_struct)) => {
                Ok(ExecStmtResult::Definition(
                    ExecDefinitionStmtResult::DefStruct(self.exec_def_struct_stmt(def_struct)?),
                ))
            }
            Stmt::Definition(DefinitionStmt::DefThmStmt(def_thm)) => {
                Ok(ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                    exec_def_thm_stmt(self, def_thm)?,
                )))
            }
            Stmt::Witness(witness_stmt) => {
                Ok(ExecStmtResult::Witness(self.exec_witness_stmt(witness_stmt)?))
            }
            Stmt::UnsafeStmt(unsafe_stmt) => {
                Ok(ExecStmtResult::Unsafe(self.exec_unsafe_stmt(unsafe_stmt)?))
            }
            Stmt::ReleaseThmStmt(stmt) => {
                Ok(ExecStmtResult::ReleaseThm(exec_release_thm_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByReflexivePropStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_reflexive_prop_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::BySymmetricPropStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_symmetric_prop_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByTransitivePropStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_transitive_prop_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByExtensionStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_extension_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_enumerate_finite_set_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByForStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_for_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByEnumerateRangeStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_enumerate_range_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByClosedRangeAsCasesStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_closed_range_as_cases_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByContraStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_contra_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByCasesStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_cases_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByDefStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_def_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByThmStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_thm_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByInducStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_induc_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByStrongInducStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_strong_induc_stmt(self, stmt)?))
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_stmt: Fact, let, have-obj-in-nonempty, have-obj-equal, have-obj-by-exist, have-fn-equal, prop, abstract_prop, struct, thm, witness, trust, release thm, by reflexive_prop / symmetric_prop / transitive_prop / extension / contra / cases / def / thm / induc / strong_induc are wired for the tracer"
                    .to_string(),
            )),
        }
    }
}
