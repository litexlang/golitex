use crate::error::{exec_stmt_error_with_stmt_and_cause, short_exec_error, RuntimeError};
use crate::infer::SuccessInferResult;
use crate::pipeline::record_pipeline_step;
use crate::result::{
    StmtResult, SuccessDefInterfaceStmtResult, SuccessDefSettingStmtResult, SuccessStmtCommonResult,
};
use crate::runtime::Runtime;
use crate::stmt::{
    ByStmt, CommandStmt, DefInterfaceStmt, DefObjStmt, DefPredicateStmt, ProofBlockStmt, Stmt,
    UnsafeStmt, WitnessStmt,
};

impl Runtime {
    pub(super) fn execute_verified_statement(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        record_pipeline_step(
            "execute",
            "Runtime::execute_verified_statement",
            "src/execute/verified_statement_execution.rs",
        );
        match stmt {
            Stmt::Fact(fact) => self.execute_submitted_fact(fact),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(s)) => self.exec_trust_stmt(s),
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(d)) => self.exec_trust_have_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::LetObjStmt(d)) => self.exec_let_obj_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(d)) => {
                self.exec_have_obj_in_nonempty_set_or_param_type_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(d)) => self.exec_have_obj_equal_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(d)) => {
                self.exec_have_obj_by_exist_facts_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromExistFact(d)) => {
                self.exec_obtain_obj_from_exist_fact(d)
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromAtomicFact(d)) => {
                self.exec_obtain_obj_from_atomic_fact(d)
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromThm(d)) => self.exec_obtain_obj_from_thm(d),
            Stmt::DefObjStmt(DefObjStmt::HaveByPreimageStmt(d)) => {
                self.exec_have_by_preimage_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(d)) => self.exec_have_fn_equal_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(d)) => {
                self.exec_have_fn_equal_case_by_case_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByInducStmt(d)) => {
                self.exec_have_fn_by_induc_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(d)) => {
                self.exec_have_fn_by_forall_exist_unique_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveTupleStmt(d)) => self.exec_have_tuple_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveCartStmt(d)) => self.exec_have_cart_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveSeqStmt(d)) => self.exec_have_seq_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveFiniteSeqStmt(d)) => self.exec_have_finite_seq_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveMatrixStmt(d)) => self.exec_have_matrix_stmt(d),
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(d)) => self.exec_def_prop_stmt(d),
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(d)) => {
                self.exec_def_abstract_prop_stmt(d)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(d)) => {
                self.exec_def_template_stmt(d)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefSettingStmt(s)) => {
                self.store_def_setting(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(SuccessDefInterfaceStmtResult::DefSettingStmt(Box::new(
                    SuccessDefSettingStmtResult {
                        statement: s.clone(),
                        common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    },
                ))
                .into())
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(s)) => {
                self.exec_def_struct_stmt(s)
            }
            Stmt::DefAlgoStmt(d) => self.exec_def_algo_stmt(d),
            Stmt::DefThmStmt(s) => self.exec_def_thm_stmt(s),
            Stmt::AxiomStmt(s) => self.exec_axiom_stmt(s),
            Stmt::DefStrategyStmt(s) => self.exec_def_strategy_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => self.exec_claim_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::ExampleStmt(s)) => self.exec_example_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => self.exec_sketch_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) => self.exec_try_stmt(s),
            Stmt::Command(CommandStmt::ImportStmt(_)) => Err(short_exec_error(
                stmt.clone(),
                "import is only valid as a top-level isolated terminal statement".to_string(),
                None,
                vec![],
            )),
            Stmt::Command(CommandStmt::ClearStmt(s)) => self.exec_clear_stmt(s),
            Stmt::Command(CommandStmt::EvalStmt(s)) => self.exec_eval_stmt(s),
            Stmt::Command(CommandStmt::UseStrategyStmt(s)) => self.exec_use_strategy_stmt(s),
            Stmt::Command(CommandStmt::StopStrategyStmt(s)) => self.exec_stop_strategy_stmt(s),
            Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => self.exec_witness_exist_fact(s),
            Stmt::Witness(WitnessStmt::WitnessAtomicFact(s)) => self.exec_witness_atomic_fact(s),
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => self.exec_witness_nonempty_set(s),
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
            Stmt::By(ByStmt::ByAntisymmetricPropStmt(s)) => self.exec_by_antisymmetric_prop_stmt(s),
            Stmt::By(ByStmt::ByZornLemmaStmt(s)) => self.exec_by_zorn_lemma_stmt(s),
            Stmt::By(ByStmt::ByAxiomOfChoiceStmt(s)) => self.exec_by_axiom_of_choice_stmt(s),
            Stmt::By(ByStmt::ByRegularityAxiomStmt(s)) => self.exec_by_regularity_axiom_stmt(s),
            Stmt::By(ByStmt::ByDefStmt(s)) => self.exec_by_def_stmt(s),
            Stmt::By(ByStmt::ByStructDefStmt(s)) => self.exec_by_struct_def_stmt(s),
            Stmt::By(ByStmt::ByThmStmt(s)) => self.exec_by_thm_stmt(s),
        }
    }
}
