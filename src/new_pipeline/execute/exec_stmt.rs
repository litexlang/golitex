use super::exec_stmt_result::{ExecDefineStmtResult, ExecIntroduceStmtResult, ExecReleaseStmtResult, ExecStmtResult};
use crate::new_pipeline::ast::stmt::{ByStmt, DefineStmt, IntroduceStmt, RegisterStmt, ReleaseStmt, Stmt};
use crate::new_pipeline::execute::execute_by_stmt::{
    exec_by_axiom_of_choice_stmt, exec_by_cases_stmt, exec_by_closed_range_as_cases_stmt,
    exec_by_contra_stmt, exec_by_def_stmt, exec_by_enumerate_finite_set_stmt,
    exec_by_enumerate_range_stmt, exec_by_extension_stmt, exec_by_fn_extension_stmt,
    exec_by_for_stmt, exec_by_induc_stmt, exec_by_regularity_axiom_stmt,
    exec_by_strong_induc_stmt, exec_by_thm_stmt, exec_by_zorn_lemma_stmt, exec_release_thm_stmt,
};
use crate::new_pipeline::execute::execute_register_stmt::{
    exec_register_reflexive_prop_stmt, exec_register_symmetric_prop_stmt,
    exec_register_transitive_prop_stmt,
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
                Stmt::Trust(_) => {
                    return Err(RuntimeError::InvalidArguments(format!(
                        "`trust` / `trust have` are forbidden under {} `-strict`",
                        crate::new_pipeline::LITEX
                    )));
                }
                Stmt::Define(DefineStmt::DefAbstractPropStmt(_)) => {
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
            Stmt::Introduce(IntroduceStmt::LetObjStmt(let_stmt)) => Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::LetObj(self.exec_let_obj(let_stmt)?),
            )),
            Stmt::Introduce(IntroduceStmt::HaveObjInNonemptySetStmt(have_stmt)) => {
                Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::HaveObjInNonemptySet(
                        self.exec_have_obj_in_nonempty_set_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Introduce(IntroduceStmt::HaveObjEqualStmt(have_stmt)) => {
                Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::HaveObjEqual(
                        self.exec_have_obj_equal_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Introduce(IntroduceStmt::HaveObjByExistFactsStmt(have_stmt)) => {
                Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::HaveObjByExistFacts(
                        self.exec_have_obj_by_exist_facts_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Introduce(IntroduceStmt::ObtainObjFromExistFact(obtain_stmt)) => {
                Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::ObtainObjFromExistFact(
                        self.exec_obtain_obj_from_exist_fact_stmt(obtain_stmt)?,
                    ),
                ))
            }
            Stmt::Introduce(IntroduceStmt::ObtainObjFromAtomicFact(obtain_stmt)) => {
                Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::ObtainObjFromAtomicFact(
                        self.exec_obtain_obj_from_atomic_fact_stmt(obtain_stmt)?,
                    ),
                ))
            }
            Stmt::Introduce(IntroduceStmt::HaveByPreimageStmt(have_stmt)) => {
                Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::HaveByFnPreimage(
                        self.exec_have_by_fn_preimage_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Introduce(IntroduceStmt::HaveByReplacementAxiomStmt(have_stmt)) => {
                Ok(ExecStmtResult::Introduce(ExecIntroduceStmtResult::HaveByReplacementAxiom(
                        self.exec_have_by_replacement_axiom_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Define(DefineStmt::HaveFnEqualStmt(have_stmt)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::HaveFnEqual(
                        self.exec_have_fn_equal_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Define(DefineStmt::HaveFnEqualCaseByCaseStmt(have_stmt)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::HaveFnEqualCaseByCase(
                        self.exec_have_fn_equal_case_by_case_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Define(DefineStmt::HaveFnByForallExistUniqueStmt(have_stmt)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::HaveFnByForallExistUnique(
                        self.exec_have_fn_by_forall_exist_unique_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Define(DefineStmt::HaveFnByInducStmt(have_stmt)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::HaveFnByInduc(
                        self.exec_have_fn_by_induc_stmt(have_stmt)?,
                    ),
                ))
            }
            Stmt::Define(DefineStmt::DefPropStmt(def_prop)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::DefProp(
                    self.exec_def_prop_stmt(def_prop)?,
                )))
            }
            Stmt::Define(DefineStmt::DefAbstractPropStmt(def_abstract_prop)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::DefAbstractProp(
                        self.exec_def_abstract_prop_stmt(def_abstract_prop)?,
                    ),
                ))
            }
            Stmt::Define(DefineStmt::DefStructStmt(def_struct)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::DefStruct(self.exec_def_struct_stmt(def_struct)?),
                ))
            }
            Stmt::Define(DefineStmt::DefTemplateStmt(def_template)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::DefTemplate(
                        self.exec_def_template_stmt(def_template)?,
                    ),
                ))
            }
            Stmt::Define(DefineStmt::DefThmStmt(def_thm)) => {
                Ok(ExecStmtResult::Define(ExecDefineStmtResult::DefThm(
                    exec_def_thm_stmt(self, def_thm)?,
                )))
            }
            Stmt::Witness(witness_stmt) => {
                Ok(ExecStmtResult::Witness(self.exec_witness_stmt(witness_stmt)?))
            }
            Stmt::Trust(unsafe_stmt) => {
                Ok(ExecStmtResult::Trust(self.exec_unsafe_stmt(unsafe_stmt)?))
            }
            Stmt::Release(ReleaseStmt::ReleaseThmStmt(stmt)) => {
                Ok(ExecStmtResult::Release(ExecReleaseStmtResult::Thm(exec_release_thm_stmt(self, stmt)?)))
            }
            Stmt::Release(ReleaseStmt::ReleaseStructDefStmt(stmt)) => Ok(ExecStmtResult::Release(ExecReleaseStmtResult::StructDef(
                self.exec_release_struct_def_stmt(stmt)?,
            ))),
            Stmt::Release(ReleaseStmt::ReleaseObjDefStmt(stmt)) => Ok(ExecStmtResult::Release(ExecReleaseStmtResult::ObjDef(
                self.exec_release_obj_def_stmt(stmt)?,
            ))),
            Stmt::Register(RegisterStmt::RegisterReflexivePropStmt(stmt)) => {
                Ok(ExecStmtResult::Register(exec_register_reflexive_prop_stmt(
                    self, stmt,
                )?))
            }
            Stmt::Register(RegisterStmt::RegisterSymmetricPropStmt(stmt)) => {
                Ok(ExecStmtResult::Register(exec_register_symmetric_prop_stmt(
                    self, stmt,
                )?))
            }
            Stmt::Register(RegisterStmt::RegisterTransitivePropStmt(stmt)) => {
                Ok(ExecStmtResult::Register(exec_register_transitive_prop_stmt(
                    self, stmt,
                )?))
            }
            Stmt::By(ByStmt::ByExtensionStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_extension_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByFnExtensionStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_fn_extension_stmt(self, stmt)?))
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
            Stmt::By(ByStmt::ByRegularityAxiomStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_regularity_axiom_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByAxiomOfChoiceStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_axiom_of_choice_stmt(self, stmt)?))
            }
            Stmt::By(ByStmt::ByZornLemmaStmt(stmt)) => {
                Ok(ExecStmtResult::By(exec_by_zorn_lemma_stmt(self, stmt)?))
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_stmt: Fact, let, have-obj-in-nonempty, have-obj-equal, have-obj-by-exist, have-fn-equal, have-fn-by-cases, have-fn-by-exist!, have-fn-by-induc, prop, abstract_prop, struct, template, thm, witness, trust, release thm, release struct def, register reflexive/symmetric/transitive, by extension / contra / cases / def / thm / induc / strong_induc / regularity_axiom / axiom_of_choice / zorn_lemma are wired for the tracer"
                    .to_string(),
            )),
        }
    }
}
