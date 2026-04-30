use crate::prelude::*;
use std::result::Result;

impl Runtime {
    /// Assume `forall` parameters and dom facts in the current environment (no extra `push_env`).
    /// Used by [`Self::verify_forall_fact`] and by `by cases` in the same `run_in_local_env` as the
    /// case branch.
    pub(crate) fn forall_assume_params_and_dom_in_current_env(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeError> {
        if let Err(e) = self.define_params_with_type(
            &forall_fact.params_def_with_type,
            false,
            ParamObjType::Forall,
        ) {
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
            self.verify_well_defined_and_store_and_infer(dom_fact.clone(), verify_state)
                .map_err(|e| {
                    let message = "failed to assume dom fact in forall".to_string();
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
                })?;
        }
        Ok(InferResult::new())
    }

    /// Verify and store each `then` clause of `forall_fact` in the current environment.
    /// `by_cases_case_label`: when set, unknown `then` messages include the active `by cases` case.
    pub(crate) fn forall_verify_then_facts_in_current_env(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
        infer_result: &mut InferResult,
        by_cases_case_label: Option<&str>,
    ) -> Result<StmtResult, RuntimeError> {
        let mut all_then_facts_are_verified_by_builtin_rules = true;
        let mut then_verification_results: Vec<StmtResult> = Vec::new();

        let then_count = forall_fact.then_facts.len();
        for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate() {
            let result = self.verify_exist_or_and_chain_atomic_fact(then_fact, verify_state)?;
            if result.is_unknown() {
                let then_one_based = then_index + 1;
                let detail = match by_cases_case_label {
                    None => format!(
                        "forall: then-fact {}/{} could not be verified (unknown): `{}`\n{}",
                        then_one_based,
                        then_count,
                        then_fact,
                        result.body_string()
                    ),
                    Some(case_s) => format!(
                        "by cases: under case `{case_s}`: forall: then-fact {then_one_based}/{then_count} could not be verified (unknown): `{then}`\n{body}",
                        case_s = case_s,
                        then_one_based = then_one_based,
                        then_count = then_count,
                        then = then_fact,
                        body = result.body_string()
                    ),
                };
                return Ok(StmtUnknown::new_with_detail(detail).into());
            }

            self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                then_fact.clone(),
            )?;

            match &result {
                StmtResult::FactualStmtSuccess(factual_verification_result) => {
                    if !factual_verification_result.is_verified_by_builtin_rules_only() {
                        all_then_facts_are_verified_by_builtin_rules = false;
                    }
                    // Do not merge then-fact verification `infers` into `infer_result` (e.g. instantiated
                    // `min(a,b) <= a` from a known forall). Each then proof is listed in
                    // `FactualStmtSuccess::inside_results` for JSON/CLI.
                }
                StmtResult::NonFactualStmtSuccess(non_factual_success) => {
                    all_then_facts_are_verified_by_builtin_rules = false;
                    infer_result.new_infer_result_inside(non_factual_success.infers.clone());
                }
                StmtResult::StmtUnknown(_) => {
                    unreachable!("stmt unknown is handled above before this match")
                }
            }
            then_verification_results.push(result);
        }

        if all_then_facts_are_verified_by_builtin_rules && !forall_fact.then_facts.is_empty() {
            let forall_infers = InferResult::from_fact(&forall_fact.clone().into());
            return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
                forall_fact.clone().into(),
                forall_infers,
                "forall: then-facts by builtin rules".to_string(),
                then_verification_results,
            ))
            .into());
        }

        infer_result.new_fact(&forall_fact.clone().into());
        let infer_for_success = std::mem::replace(infer_result, InferResult::new());
        Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source(
            forall_fact.clone().into(),
            infer_for_success,
            "".to_string(),
            None,
            Some(forall_fact.line_file.clone()),
            then_verification_results,
        ))
        .into())
    }

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
            let mut infer_result =
                rt.forall_assume_params_and_dom_in_current_env(forall_fact, verify_state)?;
            rt.forall_verify_then_facts_in_current_env(
                forall_fact,
                verify_state,
                &mut infer_result,
                None,
            )
        })
    }
}
