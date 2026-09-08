use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    /// Freeze citations used by a process-local fact verification without
    /// assigning the verification node itself a persistent `FactId`.
    pub fn attach_known_fact_ids_to_verify_fact_result(
        &self,
        result: &mut VerifyFactResult,
    ) -> Result<(), RuntimeError> {
        if let VerifyFactResult::Verified(verification) = result {
            if let Some(verification) = Rc::get_mut(verification) {
                if let Some(proof) = verification.try_proof_mut() {
                    self.attach_known_fact_ids_to_verified_by(proof)?;
                }
            }
        }
        Ok(())
    }

    /// Freeze stored-fact citations in an internal truth-proof node. This
    /// does not store the proposition or attach a statement identity.
    pub fn attach_known_fact_ids_to_prove_fact_result(
        &self,
        result: &mut ProveFactResult,
    ) -> Result<(), RuntimeError> {
        if let Some(success) = result.factual_success_mut() {
            if let Some(verification) = Rc::get_mut(&mut success.verification) {
                self.attach_known_fact_ids_to_verified_by(verification.proof_mut())?;
            }
        }
        Ok(())
    }

    pub fn attach_known_fact_ids_to_stmt_result(
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
                success.fact_id = Some(success.fact().fact_id());
            }
            self.attach_known_fact_ids_to_infer_result(&mut success.infers)?;
            if let FactStatementEvidence::Verified(verification) = &mut success.evidence {
                if let Some(verification) = Rc::get_mut(verification) {
                    // A shared node was already frozen before entering the
                    // process-local proof memo/DAG. Do not clone the proof just
                    // to repeat an identity-attachment pass.
                    if let Some(proof) = verification.try_proof_mut() {
                        self.attach_known_fact_ids_to_verified_by(proof)?;
                    }
                }
            }
        } else {
            if let SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(claim)) =
                success
            {
                self.attach_known_fact_ids_to_infer_result(&mut claim.environment_effects)?;
                self.attach_known_fact_ids_to_infer_result(&mut claim.domain.assumption_infers)?;
            } else if let Some(common) = success.common_mut() {
                self.attach_known_fact_ids_to_infer_result(&mut common.infers)?;
            }
            success.try_visit_child_results_mut(&mut |child| {
                self.attach_known_fact_ids_to_stmt_result(child)
            })?;
            success.try_visit_success_child_results_mut(&mut |child| {
                self.attach_known_fact_ids_to_success_stmt_result(child)
            })?;

            match success {
                SuccessStmtResult::Definition(SuccessDefinitionStmtResult::HaveFnEqualStmt(
                    result,
                )) if result.verification.is_some() => {
                    let verification = result.verification.as_mut().unwrap();
                    self.attach_known_fact_ids_to_infer_result(
                        &mut verification.assumption_infers,
                    )?;
                }
                SuccessStmtResult::Definition(SuccessDefinitionStmtResult::HaveSeqStmt(result))
                    if result.verification.is_some() =>
                {
                    self.attach_known_fact_ids_to_infer_result(
                        &mut result.verification.as_mut().unwrap().assumption_infers,
                    )?;
                }
                SuccessStmtResult::Definition(SuccessDefinitionStmtResult::HaveFiniteSeqStmt(
                    result,
                )) if result.verification.is_some() => {
                    self.attach_known_fact_ids_to_infer_result(
                        &mut result.verification.as_mut().unwrap().assumption_infers,
                    )?;
                }
                SuccessStmtResult::Definition(SuccessDefinitionStmtResult::HaveMatrixStmt(
                    result,
                )) if result.verification.is_some() => {
                    self.attach_known_fact_ids_to_infer_result(
                        &mut result.verification.as_mut().unwrap().assumption_infers,
                    )?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn attach_known_fact_ids_to_infer_result(
        &self,
        infer_result: &mut SuccessInferResult,
    ) -> Result<(), RuntimeError> {
        for output in infer_result.store_fact_outputs.iter_mut() {
            // A local proof environment may already have frozen the exact
            // identity of this store before that environment was popped.
            // Only fill missing identities; an ambient fact with the same
            // proposition is not the same store operation.
            if output.fact_id.is_none() {
                output.fact_id = Some(output.itself_and_why_itself_is_stored.0.fact_id());
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
                    *fact_id = Some(fact.fact_id());
                }
            }
        }
        for application in infer_result.rule_applications.iter_mut() {
            for premise in application.premises.iter_mut() {
                if premise.fact_id.is_none() {
                    premise.fact_id = Some(premise.fact.fact_id());
                }
            }
            for conclusion in application.conclusions.iter_mut() {
                if conclusion.fact_id.is_none() {
                    conclusion.fact_id = Some(conclusion.fact.fact_id());
                }
                self.attach_known_fact_ids_to_infer_result(&mut conclusion.infers)?;
            }
        }
        Ok(())
    }

    pub fn attach_known_fact_ids_to_verified_by(
        &self,
        verified_by: &mut SuccessFactProofResult,
    ) -> Result<(), RuntimeError> {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result)
            | SuccessFactProofResult::BuiltinStrategy(result) => {
                debug_assert!(result
                    .subgoals
                    .iter()
                    .all(|subgoal| subgoal.fact_id().is_none()));
            }
            SuccessFactProofResult::StoredFactCitation(_)
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
                debug_assert!(result.steps.iter().all(|step| step.fact_id().is_none()));
            }
            SuccessFactProofResult::ForallProof(result) => {
                self.attach_known_fact_ids_to_infer_result(&mut result.assumption_infers)?;
                debug_assert!(result
                    .proves
                    .iter()
                    .all(|proved| proved.result.fact_id().is_none()));
                for proved in &mut result.proves {
                    self.attach_known_fact_ids_to_infer_result(&mut proved.store.infers)?;
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
        debug_assert!(result
            .requirements
            .iter()
            .all(|requirement| requirement.result.fact_id().is_none()));
        Ok(())
    }
}
