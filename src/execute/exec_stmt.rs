use crate::prelude::*;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        if self.current_execution_is_trusted_file() {
            return self.exec_stmt_affect_environment_only(stmt);
        }

        match stmt {
            Stmt::Fact(fact) => self.exec_fact(fact),
            Stmt::UnsafeStmt(UnsafeStmt::ProofDebtStmt(s)) => self.exec_proof_debt_stmt(s),
            Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(d)) => self.exec_let_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(d)) => {
                self.exec_have_obj_in_nonempty_set_or_param_type_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(d)) => self.exec_have_obj_equal_stmt(d),
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(d)) => {
                self.exec_have_obj_by_exist_facts_stmt(d)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveByExistStmt(d)) => self.exec_have_exist_obj_stmt(d),
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
            Stmt::DefAliasStmt(DefAliasStmt::AliasPropStmt(d)) => self.exec_alias_prop_stmt(d),
            Stmt::DefAliasStmt(DefAliasStmt::AliasThmStmt(d)) => self.exec_alias_thm_stmt(d),
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(d)) => {
                self.exec_def_template_stmt(d)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(s)) => {
                self.exec_def_struct_stmt(s)
            }
            Stmt::DefAlgoStmt(d) => self.exec_def_algo_stmt(d),
            Stmt::DefThmStmt(s) => self.exec_def_thm_stmt(s),
            Stmt::DefStrategyStmt(s) => self.exec_def_strategy_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => self.exec_claim_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => self.exec_sketch_stmt(s),
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) => self.exec_try_stmt(s),
            Stmt::Command(CommandStmt::ImportStmt(s)) => self.exec_import_stmt(s),
            Stmt::Command(CommandStmt::ExportStmt(s)) => self.exec_export_stmt(s),
            Stmt::Command(CommandStmt::LocalImportStmt(s)) => self.exec_local_import_stmt(s),
            Stmt::Command(CommandStmt::DoNothingStmt(s)) => self.exec_do_nothing_stmt(s),
            Stmt::Command(CommandStmt::ClearStmt(s)) => self.exec_clear_stmt(s),
            Stmt::Command(CommandStmt::StopImportStmt(s)) => self.exec_stop_import_stmt(s),
            Stmt::Command(CommandStmt::RunFileStmt(s)) => self.exec_run_file_stmt(s),
            Stmt::Command(CommandStmt::EvalStmt(s)) => self.exec_eval_stmt(s),
            Stmt::Command(CommandStmt::EvalByStmt(s)) => self.exec_eval_by_stmt(s),
            Stmt::Command(CommandStmt::UseStrategyStmt(s)) => self.exec_use_strategy_stmt(s),
            Stmt::Command(CommandStmt::StopStrategyStmt(s)) => self.exec_stop_strategy_stmt(s),
            Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => self.exec_witness_exist_fact(s),
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => self.exec_witness_nonempty_set(s),
            Stmt::By(ByStmt::ByCasesStmt(s)) => self.exec_by_cases_stmt(s),
            Stmt::By(ByStmt::ByContraStmt(s)) => self.exec_by_contra_stmt(s),
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(s)) => {
                self.exec_by_enumerate_finite_set_stmt(s)
            }
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
            Stmt::By(ByStmt::ByThmStmt(s)) => self.exec_by_thm_stmt(s),
        }
    }

    fn exec_stmt_affect_environment_only(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        match stmt {
            Stmt::Fact(fact) => self.exec_fact_stmt_affect_environment_only(fact),
            Stmt::UnsafeStmt(UnsafeStmt::ProofDebtStmt(s)) => {
                self.exec_proof_debt_stmt_affect_environment_only(s)
            }
            Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(s)) => {
                self.exec_let_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjInNonemptySetStmt(s)) => {
                self.exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(s)) => {
                self.exec_have_obj_equal_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveObjByExistFactsStmt(s)) => {
                self.exec_have_obj_by_exist_facts_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveByExistStmt(s)) => {
                self.exec_have_exist_obj_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveByPreimageStmt(s)) => {
                self.exec_have_by_preimage_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualStmt(s)) => {
                self.exec_have_fn_equal_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnEqualCaseByCaseStmt(s)) => {
                self.exec_have_fn_equal_case_by_case_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByInducStmt(s)) => {
                self.exec_have_fn_by_induc_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(s)) => {
                self.exec_have_fn_by_forall_exist_unique_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveTupleStmt(s)) => {
                self.exec_have_tuple_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveCartStmt(s)) => {
                self.exec_have_cart_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveSeqStmt(s)) => {
                self.exec_have_seq_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveFiniteSeqStmt(s)) => {
                self.exec_have_finite_seq_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::HaveMatrixStmt(s)) => {
                self.exec_have_matrix_stmt_affect_environment_only(s)
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(s)) => {
                self.exec_def_prop_stmt_affect_environment_only(s)
            }
            Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(s)) => {
                self.exec_def_abstract_prop_stmt_affect_environment_only(s)
            }
            Stmt::DefAliasStmt(DefAliasStmt::AliasPropStmt(s)) => self.exec_alias_prop_stmt(s),
            Stmt::DefAliasStmt(DefAliasStmt::AliasThmStmt(s)) => self.exec_alias_thm_stmt(s),
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(s)) => {
                self.store_def_template(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(s)) => {
                self.store_def_struct(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::DefAlgoStmt(s) => {
                self.store_def_algo(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::DefThmStmt(s) => self.exec_def_thm_stmt_affect_environment_only(s),
            Stmt::DefStrategyStmt(s) => self.exec_def_strategy_stmt_affect_environment_only(s),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => {
                self.exec_claim_stmt_affect_environment_only(s)
            }
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(_)) => {
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(_)) => {
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::Command(CommandStmt::ImportStmt(s)) => self.exec_import_stmt(s),
            Stmt::Command(CommandStmt::ExportStmt(s)) => self.exec_export_stmt(s),
            Stmt::Command(CommandStmt::LocalImportStmt(s)) => self.exec_local_import_stmt(s),
            Stmt::Command(CommandStmt::DoNothingStmt(s)) => self.exec_do_nothing_stmt(s),
            Stmt::Command(CommandStmt::ClearStmt(s)) => self.exec_clear_stmt(s),
            Stmt::Command(CommandStmt::StopImportStmt(s)) => self.exec_stop_import_stmt(s),
            Stmt::Command(CommandStmt::RunFileStmt(s)) => self.exec_run_file_stmt(s),
            Stmt::Command(CommandStmt::EvalStmt(_)) => {
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::Command(CommandStmt::EvalByStmt(_)) => {
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::Command(CommandStmt::UseStrategyStmt(s)) => self.exec_use_strategy_stmt(s),
            Stmt::Command(CommandStmt::StopStrategyStmt(s)) => self.exec_stop_strategy_stmt(s),
            Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => {
                self.exec_witness_exist_fact_stmt_affect_environment_only(s)
            }
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => {
                self.exec_witness_nonempty_set_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByCasesStmt(s)) => self.exec_by_cases_stmt_affect_environment_only(s),
            Stmt::By(ByStmt::ByContraStmt(s)) => {
                self.exec_by_contra_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(s)) => {
                self.exec_by_enumerate_finite_set_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByInducStmt(s)) => self.exec_by_induc_stmt_affect_environment_only(s),
            Stmt::By(ByStmt::ByForStmt(s)) => self.exec_by_for_stmt_affect_environment_only(s),
            Stmt::By(ByStmt::ByExtensionStmt(s)) => {
                self.exec_by_extension_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByEnumerateRangeStmt(s)) => {
                self.exec_by_enumerate_range_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByClosedRangeAsCasesStmt(s)) => {
                self.exec_by_closed_range_as_cases_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByTransitivePropStmt(s)) => {
                self.exec_by_transitive_prop_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::BySymmetricPropStmt(s)) => {
                self.exec_by_symmetric_prop_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByReflexivePropStmt(s)) => {
                self.exec_by_reflexive_prop_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByAntisymmetricPropStmt(s)) => {
                self.exec_by_antisymmetric_prop_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByZornLemmaStmt(s)) => {
                self.exec_by_zorn_lemma_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByAxiomOfChoiceStmt(s)) => {
                self.exec_by_axiom_of_choice_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByRegularityAxiomStmt(s)) => {
                self.exec_by_regularity_axiom_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByThmStmt(s)) => self.exec_by_thm_stmt_affect_environment_only(s),
        }
    }
}
