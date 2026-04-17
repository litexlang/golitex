use crate::prelude::*;
use std::result::Result;

impl Runtime {
    /// Declare params, assume dom facts hold, then verify each then_fact.
    pub fn verify_forall_fact(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&forall_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.is_round_0() {
            return Ok(StmtResult::StmtUnknown(StmtUnknown::new()).into());
        }

        self.run_in_local_env(|rt| {
            let mut infer_result = InferResult::new();
            if let Err(e) = rt.define_params_with_type(&forall_fact.params_def_with_type, false) {
                return Err(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "failed to define parameters in forall fact".to_string(),
                    forall_fact.line_file.clone(),
                    Some(e),
                    vec![],
                ))
                .into());
            }

            for dom_fact in forall_fact.dom_facts.iter() {
                rt.verify_fact_well_defined(dom_fact, verify_state)?;

                let dom_infer_result = rt
                    .store_fact_without_well_defined_verified_and_infer(dom_fact.clone())
                    .map_err(|e| {
                        let message = "failed to assume dom fact in forall".to_string();
                        {
                            RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                                Some(Fact::from(forall_fact.clone()).into_stmt()),
                                message.clone(),
                                forall_fact.line_file.clone(),
                                Some(RuntimeError::from(UnknownRuntimeError(
                                    RuntimeErrorStruct::new(
                                        Some(Fact::from(forall_fact.clone()).into_stmt()),
                                        message,
                                        forall_fact.line_file.clone(),
                                        Some(e),
                                        vec![],
                                    ),
                                ))),
                                vec![],
                            )))
                        }
                    })?;
                infer_result.new_infer_result_inside(dom_infer_result);
            }

            let mut all_then_facts_are_verified_by_builtin_rules = true;
            let mut then_facts_builtin_verified_by_messages: Vec<String> = Vec::new();

            let then_count = forall_fact.then_facts.len();
            for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate() {
                let result = rt.verify_exist_or_and_chain_atomic_fact(then_fact, verify_state)?;
                if result.is_unknown() {
                    let then_one_based = then_index + 1;
                    return Ok((StmtUnknown::new_with_detail(format!(
                        "forall: then-fact {}/{} could not be verified (unknown): `{}`\n{}",
                        then_one_based,
                        then_count,
                        then_fact,
                        result.body_string()
                    )))
                    .into());
                }

                // 存then
                rt.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    then_fact.clone(),
                )?;

                match &result {
                    StmtResult::FactualStmtSuccess(factual_verification_result)
                        if factual_verification_result.is_verified_by_builtin_rules_only() =>
                    {
                        then_facts_builtin_verified_by_messages
                            .push(factual_verification_result.msg.clone());
                        infer_result
                            .new_infer_result_inside(factual_verification_result.infers.clone());
                    }
                    StmtResult::FactualStmtSuccess(factual_verification_result) => {
                        all_then_facts_are_verified_by_builtin_rules = false;
                        infer_result
                            .new_infer_result_inside(factual_verification_result.infers.clone());
                    }
                    StmtResult::NonFactualStmtSuccess(non_factual_success) => {
                        all_then_facts_are_verified_by_builtin_rules = false;
                        infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                    }
                    StmtResult::StmtUnknown(_) => {
                        unreachable!("stmt unknown is handled above before this match")
                    }
                }
            }

            if all_then_facts_are_verified_by_builtin_rules && !forall_fact.then_facts.is_empty() {
                let combined_verified_by_message =
                    if then_facts_builtin_verified_by_messages.len() == 1 {
                        then_facts_builtin_verified_by_messages[0].clone()
                    } else {
                        format!(
                            "forall then-facts: {}",
                            then_facts_builtin_verified_by_messages.join("; ")
                        )
                    };
                infer_result.new_fact(&forall_fact.clone().into());
                return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    forall_fact.clone().into(),
                    infer_result,
                    combined_verified_by_message,
                    Vec::new(),
                ))
                .into());
            }

            infer_result.new_fact(&forall_fact.clone().into());
            Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source(
                forall_fact.clone().into(),
                infer_result,
                "".to_string(),
                None,
                Some(forall_fact.line_file.clone()),
                Vec::new(),
            ))
            .into())
        })
    }
}
