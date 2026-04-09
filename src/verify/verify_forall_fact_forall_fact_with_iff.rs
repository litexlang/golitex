use crate::prelude::*;
use std::result::Result;

impl Runtime {
    /// Declare params, assume dom facts hold, then verify each then_fact.
    pub fn verify_forall_fact(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&Fact::ForallFact(forall_fact.clone()))
        {
            return Ok(cached_result);
        }

        self.run_in_local_env(|rt| rt.verify_forall_fact_body(forall_fact, verify_state))
    }

    fn verify_forall_fact_body(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        if let Err(e) = self.define_params_with_type(&forall_fact.params_def_with_type, false) {
            return Err(
                RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                    "failed to define parameters in forall fact".to_string(),
                    Some(e.into()),
                    forall_fact.line_file.clone(),
                ),
            );
        }

        for dom_fact in forall_fact.dom_facts.iter() {
            self.verify_exist_or_and_chain_atomic_fact_well_defined(dom_fact, verify_state)?;

            let dom_infer_result = self
                .store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact.clone(),
                )
                .map_err(|e| {
                    let message = "failed to assume dom fact in forall".to_string();
                    RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                        Fact::ForallFact(forall_fact.clone()),
                        message.clone(),
                        forall_fact.line_file.clone(),
                        Some(RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                            message,
                            forall_fact.line_file.clone(),
                            Some(Fact::ForallFact(forall_fact.clone())),
                            Some(RuntimeError::ExecStmtError(e)),
                        ).into()),
                    )
                })?;
            infer_result.new_infer_result_inside(dom_infer_result);
        }

        let mut all_then_facts_are_verified_by_builtin_rules = true;
        let mut then_facts_builtin_verified_by_messages: Vec<String> = Vec::new();

        let then_count = forall_fact.then_facts.len();
        for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate() {
            let result = self.verify_exist_or_and_chain_atomic_fact(then_fact, verify_state)?;
            if result.is_unknown() {
                let then_one_based = then_index + 1;
                let then_line_file = then_fact.line_file();
                return Err(
                    RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                        Fact::ForallFact(forall_fact.clone()),
                        format!(
                            "forall: then-fact {}/{} could not be verified (unknown):\n{}",
                            then_one_based, then_count, then_fact
                        ),
                        then_line_file,
                        None,
                    ),
                );
            }

            // 存then
            self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                then_fact.clone(),
            )?;

            match &result {
                StmtExecResult::FactualStmtSuccess(factual_verification_result)
                    if factual_verification_result.is_verified_by_builtin_rules_only() =>
                {
                    then_facts_builtin_verified_by_messages
                        .push(factual_verification_result.msg.clone());
                    infer_result
                        .new_infer_result_inside(factual_verification_result.infers.clone());
                }
                StmtExecResult::FactualStmtSuccess(factual_verification_result) => {
                    all_then_facts_are_verified_by_builtin_rules = false;
                    infer_result
                        .new_infer_result_inside(factual_verification_result.infers.clone());
                }
                StmtExecResult::NonFactualStmtSuccess(non_factual_success) => {
                    all_then_facts_are_verified_by_builtin_rules = false;
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                StmtExecResult::StmtUnknown(_) => {
                    unreachable!("stmt unknown is handled above before this match")
                }
            }
        }

        if all_then_facts_are_verified_by_builtin_rules && !forall_fact.then_facts.is_empty() {
            let combined_verified_by_message = if then_facts_builtin_verified_by_messages.len() == 1
            {
                then_facts_builtin_verified_by_messages[0].clone()
            } else {
                format!(
                    "forall then-facts: {}",
                    then_facts_builtin_verified_by_messages.join("; ")
                )
            };
            infer_result.new_fact(&Fact::ForallFact(forall_fact.clone()));
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::ForallFact(forall_fact.clone()),
                    infer_result,
                    combined_verified_by_message,
                    Vec::new(),
                ),
            ));
        }

        infer_result.new_fact(&Fact::ForallFact(forall_fact.clone()));
        Ok(StmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_known_fact_source(
                Fact::ForallFact(forall_fact.clone()),
                infer_result,
                "".to_string(),
                None,
                Some(forall_fact.line_file.clone()),
                Vec::new(),
            ),
        ))
    }

    pub fn verify_forall_fact_with_iff(
        &mut self,
        forall_iff: &ForallFactWithIff,
        verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if let Some(cached_result) = self.verify_fact_from_cache_using_display_string(
            &Fact::ForallFactWithIff(forall_iff.clone()),
        ) {
            return Ok(cached_result);
        }

        let (forall_then_implies_iff, forall_iff_implies_then) = forall_iff.to_two_forall_facts();
        let verification_steps = [&forall_then_implies_iff, &forall_iff_implies_then];
        for forall_step in verification_steps {
            let result = self.verify_forall_fact(forall_step, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }
        }

        Ok(StmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                Fact::ForallFactWithIff(forall_iff.clone()),
                "forall iff: then=>iff and iff=>then verified".to_string(),
                None,
                Some(default_line_file()),
                Vec::new(),
            ),
        ))
    }
}
