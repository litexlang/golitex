use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
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

    pub fn attach_known_fact_ids_to_verified_by(
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
}
