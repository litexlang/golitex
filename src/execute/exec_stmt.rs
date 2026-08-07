use crate::prelude::*;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        self.clear_statement_verified_atomic_facts();
        let trusted = self.current_execution_is_trusted_file();
        let result = if trusted {
            self.exec_stmt_affect_environment_only(stmt)
        } else {
            self.exec_stmt_verified(stmt)
        };
        let result = self.finish_statement_execution(result, trusted);
        self.clear_statement_verified_atomic_facts();
        result
    }

    pub(crate) fn finish_statement_execution(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        trusted: bool,
    ) -> Result<StmtResult, RuntimeError> {
        match result {
            Ok(mut result) => {
                self.attach_known_fact_ids_to_stmt_result(&mut result)?;
                let in_trusted_prefix_run = self.current_statement_is_in_trusted_prefix_run();
                let trace = if in_trusted_prefix_run && !result.is_unknown() {
                    if self.current_statement_is_cli_trusted_prefix() {
                        StatementExecutionTrace::trusted_prefix()
                    } else {
                        StatementExecutionTrace::verified(false).with_verified_status()
                    }
                } else if trusted {
                    StatementExecutionTrace::trusted()
                } else {
                    StatementExecutionTrace::verified(result.is_unknown())
                };
                let result = result.with_execution_trace(trace);
                if self.to_lean_mode && !result.is_unknown() {
                    let to_lean_ir = self.build_stmt_to_lean_ir(&result)?;
                    Ok(result.with_to_lean_ir(to_lean_ir))
                } else {
                    Ok(result)
                }
            }
            Err(error) => {
                let phase = execution_phase_for_error(&error);
                let message = error.trace_message();
                Err(error.with_execution_trace(StatementExecutionTrace::failed(phase, message)))
            }
        }
    }

    pub(crate) fn attach_known_fact_ids_to_stmt_result(
        &self,
        result: &mut StmtResult,
    ) -> Result<(), RuntimeError> {
        if let Some(success) = result.factual_success_mut() {
            if let Some(fact_id) = self.known_fact_id_for_fact(&success.stmt)? {
                success.fact_id = Some(fact_id);
            }
            self.attach_known_fact_ids_to_infer_result(&mut success.infers)?;
            self.attach_known_fact_ids_to_verified_by(&mut success.verified_by)?;
        } else if let Some(success) = result.non_factual_success_mut() {
            self.attach_known_fact_ids_to_infer_result(&mut success.infers)?;
            for inside_result in success.inside_results.iter_mut() {
                self.attach_known_fact_ids_to_stmt_result(inside_result)?;
            }
        }
        Ok(())
    }

    pub(crate) fn attach_known_fact_ids_to_infer_result(
        &self,
        infer_result: &mut InferResult,
    ) -> Result<(), RuntimeError> {
        for output in infer_result.store_fact_outputs.iter_mut() {
            if let Some(fact_id) =
                self.known_fact_id_for_fact(&output.itself_and_why_itself_is_stored.0)?
            {
                output.fact_id = Some(fact_id);
            }
        }
        Ok(())
    }

    fn attach_known_fact_ids_to_verified_by(
        &self,
        verified_by: &mut VerifiedByResult,
    ) -> Result<(), RuntimeError> {
        match verified_by {
            VerifiedByResult::BuiltinRule(result) | VerifiedByResult::BuiltinStrategy(result) => {
                for subgoal in result.subgoals.iter_mut() {
                    self.attach_known_fact_ids_to_stmt_result(subgoal)?;
                }
            }
            VerifiedByResult::Fact(result) => {
                if let Stmt::Fact(source_fact) = result.cite_what.as_ref() {
                    if let Some(fact_id) = self.known_fact_id_for_fact(source_fact)? {
                        result.source_fact_id = Some(fact_id);
                    }
                }
            }
            VerifiedByResult::KnownForallInstantiation(result) => {
                self.attach_known_fact_ids_to_known_forall(result)?;
            }
            VerifiedByResult::VerifiedBys(result) => {
                for step in result.cite_what.iter_mut() {
                    match step {
                        VerifiedBysEnum::ByBuiltinRule(result)
                        | VerifiedBysEnum::ByBuiltinStrategy(result) => {
                            for subgoal in result.subgoals.iter_mut() {
                                self.attach_known_fact_ids_to_stmt_result(subgoal)?;
                            }
                        }
                        VerifiedBysEnum::ByFact(result) => {
                            if let Stmt::Fact(source_fact) = result.cite_what.as_ref() {
                                if let Some(fact_id) = self.known_fact_id_for_fact(source_fact)? {
                                    result.source_fact_id = Some(fact_id);
                                }
                            }
                        }
                        VerifiedBysEnum::ByKnownForall(result) => {
                            self.attach_known_fact_ids_to_known_forall(&mut result.result)?;
                        }
                        VerifiedBysEnum::ByStatementMemo(_, _) => {}
                    }
                }
            }
            VerifiedByResult::ForallProof(result) => {
                self.attach_known_fact_ids_to_infer_result(&mut result.assumption_infers)?;
                for proved in result.proves.iter_mut() {
                    self.attach_known_fact_ids_to_stmt_result(proved.result.as_mut())?;
                }
            }
            VerifiedByResult::StatementMemo(_) => {}
        }
        Ok(())
    }

    fn attach_known_fact_ids_to_known_forall(
        &self,
        result: &mut KnownForallInstantiationResult,
    ) -> Result<(), RuntimeError> {
        if let Stmt::Fact(source_fact) = result.cite_what.as_ref() {
            if let Some(fact_id) = self.known_fact_id_for_fact(source_fact)? {
                result.source_fact_id = Some(fact_id);
            }
        }
        for requirement in result.requirements.iter_mut() {
            self.attach_known_fact_ids_to_stmt_result(requirement.result.as_mut())?;
        }
        Ok(())
    }

    fn exec_stmt_verified(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        match stmt {
            Stmt::Fact(fact) => self.exec_fact(fact),
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
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(d)) => {
                self.exec_def_template_stmt(d)
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefSettingStmt(s)) => {
                self.store_def_setting(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
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
            Stmt::Command(CommandStmt::ImportStmt(_)) => Err(short_exec_error(
                stmt.clone(),
                "import is only valid as a top-level isolated terminal statement".to_string(),
                None,
                vec![],
            )),
            Stmt::Command(CommandStmt::DoNothingStmt(s)) => self.exec_do_nothing_stmt(s),
            Stmt::Command(CommandStmt::ClearStmt(s)) => self.exec_clear_stmt(s),
            Stmt::Command(CommandStmt::EvalStmt(s)) => self.exec_eval_stmt(s),
            Stmt::Command(CommandStmt::UseStrategyStmt(s)) => self.exec_use_strategy_stmt(s),
            Stmt::Command(CommandStmt::StopStrategyStmt(s)) => self.exec_stop_strategy_stmt(s),
            Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => self.exec_witness_exist_fact(s),
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
            Stmt::By(ByStmt::ByThmStmt(s)) => self.exec_by_thm_stmt(s),
        }
    }

    pub(crate) fn exec_preverified_stmt_affect_environment_only(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        // Reuse the no-verification environment path for a statement whose
        // generic form was already checked before capture-avoiding substitution.
        let previous_execution_mode = self.replace_current_execution_mode(ExecutionMode::Trusted);
        let result = self.exec_stmt_affect_environment_only(stmt);
        self.replace_current_execution_mode(previous_execution_mode);
        result
    }

    fn exec_stmt_affect_environment_only(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        match stmt {
            Stmt::Fact(fact) => self.exec_fact_stmt_affect_environment_only(fact),
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(s)) => {
                self.exec_trust_stmt_affect_environment_only(s)
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(s)) => {
                self.exec_trust_have_stmt_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::LetObjStmt(s)) => {
                self.exec_let_obj_stmt_affect_environment_only(s)
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
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(s)) => {
                self.store_def_template(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefSettingStmt(s)) => {
                self.store_def_setting(s)
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
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(s))
                if self.current_statement_is_cli_trusted_prefix() =>
            {
                self.exec_try_stmt(s)
            }
            Stmt::ProofBlock(ProofBlockStmt::SketchStmt(_))
            | Stmt::ProofBlock(ProofBlockStmt::TryStmt(_))
            | Stmt::Command(CommandStmt::EvalStmt(_)) => {
                Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into())
            }
            Stmt::Command(CommandStmt::ImportStmt(_)) => Err(short_exec_error(
                stmt.clone(),
                "import is only valid as a top-level isolated terminal statement".to_string(),
                None,
                vec![],
            )),
            Stmt::Command(CommandStmt::DoNothingStmt(s)) => self.exec_do_nothing_stmt(s),
            Stmt::Command(CommandStmt::ClearStmt(s)) => self.exec_clear_stmt(s),
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
            Stmt::By(ByStmt::ByThmStmt(s)) => self.exec_by_thm_stmt_affect_environment_only(s),
        }
    }
}

fn execution_phase_for_error(error: &RuntimeError) -> StatementExecutionPhase {
    match error {
        RuntimeError::StoreFactError(_) | RuntimeError::InferError(_) => {
            StatementExecutionPhase::AffectEnvironment
        }
        RuntimeError::WellDefinedError(_)
        | RuntimeError::DefineParamsError(_)
        | RuntimeError::InstantiateError(_)
        | RuntimeError::NameAlreadyUsedError(_) => StatementExecutionPhase::VerifyWellDefinedness,
        RuntimeError::ExecStmtError(error) => {
            if let Some(previous_error) = error.previous_error.as_ref() {
                return execution_phase_for_error(previous_error);
            }
            StatementExecutionPhase::VerifyProcess
        }
        RuntimeError::ArithmeticError(_)
        | RuntimeError::NewFactError(_)
        | RuntimeError::ParseError(_)
        | RuntimeError::VerifyError(_)
        | RuntimeError::UnknownError(_) => StatementExecutionPhase::VerifyProcess,
    }
}
