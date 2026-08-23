use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        self.exec_stmt_with_trusted_prefix_context(stmt, false)
    }

    pub(crate) fn exec_stmt_in_trusted_prefix_run(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_stmt_with_trusted_prefix_context(stmt, true)
    }

    fn exec_stmt_with_trusted_prefix_context(
        &mut self,
        stmt: &Stmt,
        in_trusted_prefix_run: bool,
    ) -> Result<StmtResult, RuntimeError> {
        self.clear_statement_proof_state();
        let trusted = self.current_execution_is_trusted_file();
        let result = if trusted {
            self.exec_stmt_affect_environment_only(stmt, in_trusted_prefix_run)
        } else {
            self.exec_stmt_verified(stmt)
        };
        let result = self.finish_statement_execution_with_trusted_prefix_context(
            result,
            trusted,
            in_trusted_prefix_run,
        );
        self.clear_statement_proof_state();
        result
    }

    pub(crate) fn finish_statement_execution(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        trusted: bool,
    ) -> Result<StmtResult, RuntimeError> {
        self.finish_statement_execution_with_trusted_prefix_context(result, trusted, false)
    }

    pub(crate) fn finish_statement_execution_in_trusted_prefix_run(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        trusted: bool,
    ) -> Result<StmtResult, RuntimeError> {
        self.finish_statement_execution_with_trusted_prefix_context(result, trusted, true)
    }

    fn finish_statement_execution_with_trusted_prefix_context(
        &mut self,
        result: Result<StmtResult, RuntimeError>,
        trusted: bool,
        in_trusted_prefix_run: bool,
    ) -> Result<StmtResult, RuntimeError> {
        match result {
            Ok(mut result) => {
                self.attach_known_fact_ids_to_stmt_result(&mut result)?;
                let trace = if in_trusted_prefix_run && !result.is_unknown() {
                    if trusted {
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
                Ok(result)
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
        if let StmtResult::Success(success) = result {
            self.attach_known_fact_ids_to_success_stmt_result(success)?;
        }
        Ok(())
    }

    fn attach_known_fact_ids_to_success_stmt_result(
        &self,
        success: &mut SuccessStmtResult,
    ) -> Result<(), RuntimeError> {
        if let SuccessStmtResult::Fact(success) = success {
            // A nested proof result may already carry the exact FactId from a
            // local environment that has since been popped. Never retarget it
            // to a later ambient fact with the same proposition.
            if success.fact_id.is_none() {
                if let Some(fact_id) = self.known_fact_id_for_fact(&success.fact())? {
                    success.fact_id = Some(fact_id);
                }
            }
            self.attach_known_fact_ids_to_infer_result(&mut success.infers)?;
            if let Some(verification) = Rc::get_mut(&mut success.verification) {
                self.attach_known_fact_ids_to_verified_by(verification.proof_mut())?;
            }
        } else {
            if let Some(common) = success.common_mut() {
                self.attach_known_fact_ids_to_infer_result(&mut common.infers)?;
            }
            success.try_visit_child_results_mut(&mut |child| {
                self.attach_known_fact_ids_to_stmt_result(child)
            })?;
            success.try_visit_success_child_results_mut(&mut |child| {
                self.attach_known_fact_ids_to_success_stmt_result(child)
            })?;

            match success {
                SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveFnEqualStmt(result))
                    if result.verification.is_some() =>
                {
                    let verification = result.verification.as_mut().unwrap();
                    self.attach_known_fact_ids_to_infer_result(
                        &mut verification.assumption_infers,
                    )?;
                }
                SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveSeqStmt(result))
                    if result.verification.is_some() =>
                {
                    self.attach_known_fact_ids_to_infer_result(
                        &mut result.verification.as_mut().unwrap().assumption_infers,
                    )?;
                }
                SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveFiniteSeqStmt(
                    result,
                )) if result.verification.is_some() => {
                    self.attach_known_fact_ids_to_infer_result(
                        &mut result.verification.as_mut().unwrap().assumption_infers,
                    )?;
                }
                SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveMatrixStmt(result))
                    if result.verification.is_some() =>
                {
                    self.attach_known_fact_ids_to_infer_result(
                        &mut result.verification.as_mut().unwrap().assumption_infers,
                    )?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub(crate) fn attach_known_fact_ids_to_infer_result(
        &self,
        infer_result: &mut SuccessInferResult,
    ) -> Result<(), RuntimeError> {
        for output in infer_result.store_fact_outputs.iter_mut() {
            // A local proof environment may already have frozen the exact
            // identity of this store before that environment was popped.
            // Only fill missing identities; an ambient fact with the same
            // proposition is not the same store operation.
            if output.fact_id.is_none() {
                output.fact_id =
                    self.known_fact_id_for_fact(&output.itself_and_why_itself_is_stored.0)?;
            }
            if output.inferred_fact_ids.len() != output.inferred_facts.len() {
                return Err(RuntimeError::from(UnknownRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "inferred fact identity list does not match inferred facts".to_string(),
                        output.itself_and_why_itself_is_stored.0.line_file(),
                        None,
                        vec![],
                    ),
                )));
            }
            for (fact, fact_id) in output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter_mut())
            {
                if fact_id.is_none() {
                    *fact_id = self.known_fact_id_for_fact(fact)?;
                }
            }
        }
        for application in infer_result.rule_applications.iter_mut() {
            for premise in application.premises.iter_mut() {
                if premise.fact_id.is_none() {
                    premise.fact_id = self.known_fact_id_for_fact(&premise.fact)?;
                }
            }
            for conclusion in application.conclusions.iter_mut() {
                if conclusion.fact_id.is_none() {
                    conclusion.fact_id = self.known_fact_id_for_fact(&conclusion.fact)?;
                }
                self.attach_known_fact_ids_to_infer_result(&mut conclusion.infers)?;
            }
        }
        Ok(())
    }

    pub(crate) fn attach_known_fact_ids_to_verified_by(
        &self,
        verified_by: &mut SuccessFactProofResult,
    ) -> Result<(), RuntimeError> {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result)
            | SuccessFactProofResult::BuiltinStrategy(result) => {
                for subgoal in result.subgoals.iter_mut() {
                    self.attach_known_fact_ids_to_stmt_result(subgoal)?;
                }
            }
            SuccessFactProofResult::StoredFactCitation(_)
            | SuccessFactProofResult::Strategy(_)
            | SuccessFactProofResult::DefinitionReduction(_)
            | SuccessFactProofResult::CheckedFunctionDefinitionReduction(_)
            | SuccessFactProofResult::DiagnosticOnly(_) => {}
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                self.attach_known_fact_ids_to_known_forall(result)?;
            }
            SuccessFactProofResult::CombinedProofs(result) => {
                if let Some(primary) = result.primary.as_mut() {
                    if let Some(primary) = Rc::get_mut(primary) {
                        self.attach_known_fact_ids_to_verified_by(primary.proof_mut())?;
                    }
                }
                for step in result.steps.iter_mut() {
                    self.attach_known_fact_ids_to_stmt_result(step)?;
                }
            }
            SuccessFactProofResult::ForallProof(result) => {
                self.attach_known_fact_ids_to_infer_result(&mut result.assumption_infers)?;
                for proved in result.proves.iter_mut() {
                    self.attach_known_fact_ids_to_stmt_result(proved.result.as_mut())?;
                }
            }
            SuccessFactProofResult::Transform(_result) => {
                // The transform child is shared proof evidence. Its producer
                // freezes citation identities before constructing this Rc;
                // post-hoc mutation must not clone or flatten that child.
            }
            SuccessFactProofResult::Reuse(_) => {}
        }
        Ok(())
    }

    fn attach_known_fact_ids_to_known_forall(
        &self,
        result: &mut SuccessInstantiateKnownForallResult,
    ) -> Result<(), RuntimeError> {
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
            Stmt::Command(CommandStmt::DoNothingStmt(s)) => self.exec_do_nothing_stmt(s),
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

    pub(crate) fn exec_preverified_stmt_affect_environment_only(
        &mut self,
        stmt: &Stmt,
    ) -> Result<StmtResult, RuntimeError> {
        if let Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(s)) = stmt {
            return Err(short_exec_error(
                s.clone().into(),
                "a template declaration cannot be replayed as a preverified template body",
                None,
                vec![],
            ));
        }
        // Reuse the no-verification environment path for a statement whose
        // generic form was already checked before capture-avoiding substitution.
        let previous_execution_mode = self.replace_current_execution_mode(ExecutionMode::Trusted);
        let result = self.exec_stmt_affect_environment_only(stmt, false);
        self.replace_current_execution_mode(previous_execution_mode);
        result
    }

    fn exec_stmt_affect_environment_only(
        &mut self,
        stmt: &Stmt,
        in_trusted_prefix_run: bool,
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
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromExistFact(s)) => {
                self.exec_obtain_obj_from_exist_fact_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromAtomicFact(s)) => {
                self.exec_obtain_obj_from_atomic_fact_affect_environment_only(s)
            }
            Stmt::DefObjStmt(DefObjStmt::ObtainObjFromThm(s)) => {
                self.exec_obtain_obj_from_thm_affect_environment_only(s)
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
            // A trusted file still reconstructs the retained verification
            // evidence for a public template declaration. Template instances
            // consume that generic evidence after capture-avoiding
            // substitution, so storing only the syntax would make the Result
            // contract incomplete.
            Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(s)) => {
                let previous_execution_mode =
                    self.replace_current_execution_mode(ExecutionMode::Verified);
                let result = self.exec_def_template_stmt(s);
                self.replace_current_execution_mode(previous_execution_mode);
                result
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
                self.store_def_struct(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(SuccessDefInterfaceStmtResult::DefStructStmt(Box::new(
                    SuccessDefStructStmtResult {
                        statement: s.clone(),
                        common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    },
                ))
                .into())
            }
            Stmt::DefAlgoStmt(s) => {
                self.store_def_algo(s)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
                Ok(
                    SuccessStmtResult::DefAlgoStmt(Box::new(SuccessDefAlgoStmtResult {
                        statement: s.clone(),
                        common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    }))
                    .into(),
                )
            }
            Stmt::DefThmStmt(s) => self.exec_def_thm_stmt_affect_environment_only(s),
            Stmt::AxiomStmt(s) => self.exec_axiom_stmt_affect_environment_only(s),
            Stmt::DefStrategyStmt(s) => self.exec_def_strategy_stmt_affect_environment_only(s),
            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => {
                self.exec_claim_stmt_affect_environment_only(s)
            }
            Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) if in_trusted_prefix_run => {
                self.exec_try_stmt(s)
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
                    proof: None,
                }))
                .into(),
            ),
            Stmt::Command(CommandStmt::EvalStmt(s)) => Ok(SuccessCommandStmtResult::EvalStmt(
                Box::new(SuccessEvalStmtResult {
                    statement: s.clone(),
                    common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    execution: SuccessEvalStmtExecutionResult::SkippedByTrustedPrefix,
                }),
            )
            .into()),
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
            Stmt::Witness(WitnessStmt::WitnessAtomicFact(s)) => {
                self.exec_witness_atomic_fact_stmt_affect_environment_only(s)
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
            Stmt::By(ByStmt::ByStructDefStmt(s)) => {
                self.exec_by_struct_def_stmt_affect_environment_only(s)
            }
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
