use crate::error::{exec_stmt_error_with_stmt_and_cause, RuntimeError};
use crate::inference::SuccessInferResult;
use crate::result::{
    StmtResult, SuccessDefSettingStmtResult, SuccessDefinitionStmtResult, SuccessStmtCommonResult,
};
use crate::runtime::Runtime;
use crate::statement::{
    ByStmt, CommandStmt, DefinitionStmt, ProofBlockStmt, Stmt, UnsafeStmt, WitnessStmt,
};

impl Runtime {
    pub(super) fn execute_statement_with_verification(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result = self.execute_statement_with_verification_body(stmt)?;
        self.attach_known_fact_ids_to_stmt_result(&mut result)?;
        Ok(result)
    }

    fn execute_statement_with_verification_body(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        match stmt {
            Stmt::Fact(fact) => self.execute_submitted_fact(fact),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(s)) => self.exec_trust_stmt(s),
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(d)) => self.exec_trust_have_stmt(d),
            Stmt::Definition(DefinitionStmt::LetObjStmt(d)) => self.exec_let_obj_stmt(d),
            Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(d)) => {
                self.exec_have_obj_in_nonempty_set_or_param_type_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(d)) => {
                self.exec_have_obj_equal_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(d)) => {
                self.exec_have_obj_by_exist_facts_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromExistFact(d)) => {
                self.exec_obtain_obj_from_exist_fact(d)
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromAtomicFact(d)) => {
                self.exec_obtain_obj_from_atomic_fact(d)
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromThm(d)) => {
                self.exec_obtain_obj_from_thm(d)
            }
            Stmt::Definition(DefinitionStmt::HaveByPreimageStmt(d)) => {
                self.exec_have_by_preimage_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(d)) => self.exec_have_fn_equal_stmt(d),
            Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(d)) => {
                self.exec_have_fn_equal_case_by_case_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::HaveFnByInducStmt(d)) => {
                self.exec_have_fn_by_induc_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::HaveFnByForallExistUniqueStmt(d)) => {
                self.exec_have_fn_by_forall_exist_unique_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::DefPropStmt(d)) => self.exec_def_prop_stmt(d),
            Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(d)) => {
                self.exec_def_abstract_prop_stmt(d)
            }
            Stmt::Definition(DefinitionStmt::DefTemplateStmt(d)) => self.exec_def_template_stmt(d),
            Stmt::Definition(DefinitionStmt::DefSettingStmt(s)) => {
                self.store_def_setting(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(SuccessDefinitionStmtResult::DefSettingStmt(Box::new(
                    SuccessDefSettingStmtResult {
                        statement: s.clone(),
                        common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    },
                ))
                .into())
            }
            Stmt::Definition(DefinitionStmt::DefStructStmt(s)) => self.exec_def_struct_stmt(s),
            Stmt::Definition(DefinitionStmt::DefAlgoStmt(d)) => self.exec_def_algo_stmt(d),
            Stmt::Definition(DefinitionStmt::DefThmStmt(s)) => self.exec_def_thm_stmt(s),
            Stmt::Definition(DefinitionStmt::AxiomStmt(s)) => self.exec_axiom_stmt(s),
            Stmt::Definition(DefinitionStmt::DefStrategyStmt(s)) => self.exec_def_strategy_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => self.exec_claim_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::ExampleStmt(s)) => self.exec_example_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => self.exec_sketch_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) => self.exec_try_stmt(s),
            Stmt::Command(CommandStmt::EvalStmt(s)) => self.exec_eval_stmt(s),
            Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => self.exec_witness_exist_fact(s),
            Stmt::Witness(WitnessStmt::WitnessAtomicFact(s)) => self.exec_witness_atomic_fact(s),
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => self.exec_witness_nonempty_set(s),
            Stmt::ReleaseThmStmt(s) => self.exec_release_thm_stmt(s),
            Stmt::By(ByStmt::ByCasesStmt(s)) => self.exec_by_cases_stmt(s),
            Stmt::By(ByStmt::ByContraStmt(s)) => self.exec_by_contra_stmt(s),
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(s)) => {
                self.exec_by_enumerate_finite_set_stmt(s)
            }
            Stmt::By(ByStmt::ByFiniteSetInducStmt(s)) => self.exec_by_finite_set_induc_stmt(s),
            Stmt::By(ByStmt::ByInducStmt(s)) => self.exec_by_induc_stmt(s),
            Stmt::By(ByStmt::ByForStmt(s)) => self.exec_by_for_stmt(s),
            Stmt::By(ByStmt::ByExtensionStmt(s)) => self.exec_by_extension_stmt(s),
            Stmt::By(ByStmt::ByEnumerateRangeStmt(s)) => self.exec_by_enumerate_range_stmt(s),
            Stmt::By(ByStmt::ByClosedRangeAsCasesStmt(s)) => {
                self.exec_by_closed_range_as_cases_stmt(s)
            }
            Stmt::By(ByStmt::ByTransitivePropStmt(s)) => self.exec_by_transitive_prop_stmt(s),
            Stmt::By(ByStmt::BySymmetricPropStmt(s)) => self.exec_by_symmetric_prop_stmt(s),
            Stmt::By(ByStmt::ByReflexivePropStmt(s)) => self.exec_by_reflexive_prop_stmt(s),
            Stmt::By(ByStmt::ByZornLemmaStmt(s)) => self.exec_by_zorn_lemma_stmt(s),
            Stmt::By(ByStmt::ByAxiomOfChoiceStmt(s)) => self.exec_by_axiom_of_choice_stmt(s),
            Stmt::By(ByStmt::ByRegularityAxiomStmt(s)) => self.exec_by_regularity_axiom_stmt(s),
            Stmt::By(ByStmt::ByDefStmt(s)) => self.exec_by_def_stmt(s),
            Stmt::ReleaseStructDefStmt(s) => self.exec_release_struct_def_stmt(s),
            Stmt::By(ByStmt::ByThmStmt(s)) => self.exec_by_thm_stmt(s),
        }
    }
}
