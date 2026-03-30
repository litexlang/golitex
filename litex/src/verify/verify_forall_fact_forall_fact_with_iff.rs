use crate::prelude::*;
use std::result::Result;

impl Runtime {
    /// Declare params, assume dom facts hold, then verify each then_fact.
    pub fn verify_forall_fact(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&Fact::ForallFact(forall_fact.clone()))
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_forall_fact_well_defined(forall_fact, verify_state) {
                return Err(VerifyError::new(
                    Fact::ForallFact(forall_fact.clone()),
                    String::new(),
                    forall_fact.line_file,
                    Some(RuntimeError::WellDefinedError(e)),
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        self.push_env();
        let result = self.verify_forall_fact_body(forall_fact, &verify_state_for_children);
        self.pop_env();

        result
    }

    fn verify_forall_fact_body(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut infer_result = InferResult::new();
        for param_def in forall_fact.params_def_with_type.iter() {
            let param_infer_result = self
                .define_params_with_type(std::slice::from_ref(param_def), false)
                .map_err(|e| {
                    let message = "failed to define params in forall".to_string();
                    VerifyError::new(
                        Fact::ForallFact(forall_fact.clone()),
                        message.clone(),
                        forall_fact.line_file,
                        Some(RuntimeError::UnknownError(UnknownError::new(
                            message,
                            forall_fact.line_file,
                            Some(Fact::ForallFact(forall_fact.clone())),
                            Some(RuntimeError::DefineParamsError(e)),
                        ))),
                    )
                })?;
            infer_result.new_infer_result_inside(param_infer_result);
        }

        for dom_fact in forall_fact.dom_facts.iter() {
            let dom_infer_result = self
                .store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact,
                )
                .map_err(|e| {
                    let message = "failed to assume dom fact in forall".to_string();
                    VerifyError::new(
                        Fact::ForallFact(forall_fact.clone()),
                        message.clone(),
                        forall_fact.line_file,
                        Some(RuntimeError::UnknownError(UnknownError::new(
                            message,
                            forall_fact.line_file,
                            Some(Fact::ForallFact(forall_fact.clone())),
                            Some(RuntimeError::StoreFactError(e)),
                        ))),
                    )
                })?;
            infer_result.new_infer_result_inside(dom_infer_result);
        }

        let mut all_then_facts_are_verified_by_builtin_rules = true;
        let mut then_facts_builtin_verified_by_messages: Vec<String> = Vec::new();

        for then_fact in forall_fact.then_facts.iter() {
            let result = self.verify_exist_or_and_chain_atomic_fact(then_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }

            match &result {
                NonErrStmtExecResult::FactualStmtSuccess(factual_verification_result)
                    if factual_verification_result.is_verified_by_builtin_rules_only() =>
                {
                    then_facts_builtin_verified_by_messages
                        .push(factual_verification_result.msg.clone());
                    infer_result
                        .new_infer_result_inside(factual_verification_result.infers.clone());
                }
                NonErrStmtExecResult::FactualStmtSuccess(factual_verification_result) => {
                    all_then_facts_are_verified_by_builtin_rules = false;
                    infer_result
                        .new_infer_result_inside(factual_verification_result.infers.clone());
                }
                NonErrStmtExecResult::NonFactualStmtSuccess(non_factual_success) => {
                    all_then_facts_are_verified_by_builtin_rules = false;
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                NonErrStmtExecResult::StmtUnknown(_) => {
                    return Ok(result);
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
            return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::ForallFact(forall_fact.clone()),
                    infer_result,
                    combined_verified_by_message,
                    Vec::new(),
                ),
            ));
        }

        Ok(NonErrStmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_known_fact_source(
                Fact::ForallFact(forall_fact.clone()),
                infer_result,
                "".to_string(),
                None,
                Some(forall_fact.line_file),
                Vec::new(),
            ),
        ))
    }

    /// Forall iff: two steps. Step 1: take then as part of dom, verify iff. Step 2: take iff as part of dom, verify then.
    pub fn verify_forall_fact_with_iff(
        &mut self,
        forall_iff: &ForallFactWithIff,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(cached_result) = self.verify_fact_from_cache_using_display_string(
            &Fact::ForallFactWithIff(forall_iff.clone()),
        ) {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_forall_fact_with_iff_well_defined(forall_iff, verify_state)
            {
                return Err(VerifyError::new(
                    Fact::ForallFactWithIff(forall_iff.clone()),
                    String::new(),
                    forall_iff.line_file,
                    Some(RuntimeError::WellDefinedError(e)),
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let f = &forall_iff.forall_fact;

        let mut dom_then = f.dom_facts.clone();
        dom_then.extend(f.then_facts.clone());
        let forall_then_implies_iff = ForallFact::new(
            f.params_def_with_type.clone(),
            dom_then,
            forall_iff.iff_facts.clone(),
            forall_iff.line_file,
        );
        let result1 =
            self.verify_forall_fact(&forall_then_implies_iff, &verify_state_for_children)?;
        if result1.is_unknown() {
            return Ok(result1);
        }

        let mut dom_iff = f.dom_facts.clone();
        dom_iff.extend(forall_iff.iff_facts.clone());
        let forall_iff_implies_then = ForallFact::new(
            f.params_def_with_type.clone(),
            dom_iff,
            f.then_facts.clone(),
            forall_iff.line_file,
        );
        let result2 =
            self.verify_forall_fact(&forall_iff_implies_then, &verify_state_for_children)?;
        if result2.is_unknown() {
            return Ok(result2);
        }

        Ok(NonErrStmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_known_fact_source(
                Fact::ForallFactWithIff(forall_iff.clone()),
                InferResult::new(),
                "forall iff: then=>iff and iff=>then verified".to_string(),
                None,
                Some(DEFAULT_LINE_FILE),
                Vec::new(),
            ),
        ))
    }
}
