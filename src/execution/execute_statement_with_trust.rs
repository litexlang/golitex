use crate::error::{exec_stmt_error_with_stmt_and_cause, short_exec_error, RuntimeError};
use crate::inference::SuccessInferResult;
use crate::result::{
    StmtResult, SuccessCommandStmtResult, SuccessDefAlgoStmtResult, SuccessDefSettingStmtResult,
    SuccessDefStructStmtResult, SuccessDefinitionStmtResult, SuccessEvalStmtExecutionResult,
    SuccessEvalStmtResult, SuccessExampleStmtResult, SuccessProofBlockStmtResult,
    SuccessSketchStmtResult, SuccessStmtCommonResult, SuccessStmtResult, SuccessTryStmtResult,
    TryStmtExecutionResult,
};
use crate::runtime::{ExecutionMode, Runtime};
use crate::statement::{
    ByStmt, CommandStmt, DefinitionStmt, ProofBlockStmt, Stmt, UnsafeStmt, WitnessStmt,
};

impl Runtime {
    pub(super) fn execute_statement_with_trust(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result = self.execute_statement_with_trust_body(stmt)?;
        self.attach_known_fact_ids_to_stmt_result(&mut result)?;
        Ok(result)
    }

    pub fn execute_statement_with_prior_verification(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        if let Stmt::Definition(DefinitionStmt::DefTemplateStmt(s)) = stmt {
            return Err(short_exec_error(
                s.clone().into(),
                "a template definition cannot be replayed as a preverified template body",
                None,
                vec![],
            ));
        }
        // Reuse the no-verification environment path for a statement whose
        // generic form was already checked before capture-avoiding substitution.
        let previous_execution_mode = self.replace_current_execution_mode(ExecutionMode::Trusted);
        let result = self.execute_statement_with_trust_body(stmt);
        self.replace_current_execution_mode(previous_execution_mode);
        result
    }

    pub(super) fn execute_statement_with_trust_body(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        match stmt {
            Stmt::Fact(fact) => self.execute_fact_with_trust(fact),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(s)) => {
                self.exec_trust_stmt_affect_environment_only(s)
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(s)) => {
                self.exec_trust_have_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::LetObjStmt(s)) => {
                self.exec_let_obj_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveObjInNonemptySetStmt(s)) => {
                self.exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(s)) => {
                self.exec_have_obj_equal_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveObjByExistFactsStmt(s)) => {
                self.exec_have_obj_by_exist_facts_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromExistFact(s)) => {
                self.exec_obtain_obj_from_exist_fact_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromAtomicFact(s)) => {
                self.exec_obtain_obj_from_atomic_fact_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::ObtainObjFromThm(s)) => {
                self.exec_obtain_obj_from_thm_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveByPreimageStmt(s)) => {
                self.exec_have_by_preimage_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualStmt(s)) => {
                self.exec_have_fn_equal_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveFnEqualCaseByCaseStmt(s)) => {
                self.exec_have_fn_equal_case_by_case_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveFnByInducStmt(s)) => {
                self.exec_have_fn_by_induc_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveFnByForallExistUniqueStmt(s)) => {
                self.exec_have_fn_by_forall_exist_unique_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveTupleStmt(s)) => {
                self.exec_have_tuple_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveCartStmt(s)) => {
                self.exec_have_cart_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveSeqStmt(s)) => {
                self.exec_have_seq_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveFiniteSeqStmt(s)) => {
                self.exec_have_finite_seq_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::HaveMatrixStmt(s)) => {
                self.exec_have_matrix_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::DefPropStmt(s)) => {
                self.exec_def_prop_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::DefAbstractPropStmt(s)) => {
                self.exec_def_abstract_prop_stmt_affect_environment_only(s)
            }
            // A trusted file still reconstructs the retained verification
            // evidence for a public template definition. Template instances
            // consume that generic evidence after capture-avoiding
            // substitution, so storing only the syntax would make the Result
            // contract incomplete.
            Stmt::Definition(DefinitionStmt::DefTemplateStmt(s)) => {
                let previous_execution_mode =
                    self.replace_current_execution_mode(ExecutionMode::RequireVerification);
                let result = self.exec_def_template_stmt(s);
                self.replace_current_execution_mode(previous_execution_mode);
                result
            }
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
            Stmt::Definition(DefinitionStmt::DefStructStmt(s)) => {
                self.store_def_struct(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(SuccessDefinitionStmtResult::DefStructStmt(Box::new(
                    SuccessDefStructStmtResult {
                        statement: s.clone(),
                        common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                        run_in_local_env: None,
                    },
                ))
                .into())
            }
            Stmt::Definition(DefinitionStmt::DefAlgoStmt(s)) => {
                self.store_def_algo(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(
                    SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefAlgoStmt(
                        Box::new(SuccessDefAlgoStmtResult {
                            statement: s.clone(),
                            common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                            run_in_local_env: None,
                        }),
                    ))
                    .into(),
                )
            }
            Stmt::Definition(DefinitionStmt::DefThmStmt(s)) => {
                self.exec_def_thm_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::AxiomStmt(s)) => {
                self.exec_axiom_stmt_affect_environment_only(s)
            }
            Stmt::Definition(DefinitionStmt::DefStrategyStmt(s)) => {
                self.exec_def_strategy_stmt_affect_environment_only(s)
            }
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => {
                self.exec_claim_stmt_affect_environment_only(s)
            }
            Stmt::ProofBlock(ProofBlockStmt::ExampleStmt(s)) => Ok(
                SuccessProofBlockStmtResult::ExampleStmt(Box::new(SuccessExampleStmtResult {
                    statement: s.clone(),
                    common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    verification: None,
                }))
                .into(),
            ),
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => Ok(
                SuccessProofBlockStmtResult::SketchStmt(Box::new(SuccessSketchStmtResult {
                    statement: s.clone(),
                    common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    proof: None,
                }))
                .into(),
            ),
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) => Ok(
                SuccessProofBlockStmtResult::TryStmt(Box::new(SuccessTryStmtResult {
                    statement: s.clone(),
                    common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    execution: TryStmtExecutionResult::SkippedByTrustedExecution,
                }))
                .into(),
            ),
            Stmt::Command(CommandStmt::EvalStmt(s)) => Ok(SuccessCommandStmtResult::EvalStmt(
                Box::new(SuccessEvalStmtResult {
                    statement: s.clone(),
                    common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    execution: SuccessEvalStmtExecutionResult::SkippedByTrustedExecution,
                }),
            )
            .into()),
            Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => {
                self.exec_witness_exist_fact_stmt_affect_environment_only(s)
            }
            Stmt::Witness(WitnessStmt::WitnessAtomicFact(s)) => {
                self.exec_witness_atomic_fact_stmt_affect_environment_only(s)
            }
            Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => {
                self.exec_witness_nonempty_set_stmt_affect_environment_only(s)
            }
            Stmt::ReleaseThmStmt(s) => self.exec_release_thm_stmt_affect_environment_only(s),
            Stmt::By(ByStmt::ByCasesStmt(s)) => self.exec_by_cases_stmt_affect_environment_only(s),
            Stmt::By(ByStmt::ByContraStmt(s)) => {
                self.exec_by_contra_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(s)) => {
                self.exec_by_enumerate_finite_set_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByFiniteSetInducStmt(s)) => {
                self.exec_by_finite_set_induc_stmt_affect_environment_only(s)
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
            Stmt::By(ByStmt::ByDefStmt(s)) => self.exec_by_def_stmt_affect_environment_only(s),
            Stmt::By(ByStmt::ByStructDefStmt(s)) => {
                self.exec_by_struct_def_stmt_affect_environment_only(s)
            }
            Stmt::By(ByStmt::ByThmStmt(s)) => self.exec_by_thm_stmt_affect_environment_only(s),
        }
    }
}
