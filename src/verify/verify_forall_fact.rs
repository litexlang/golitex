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
        let mut assumption_infer_result = self
            .define_params_with_type(
                &forall_fact.params_def_with_type,
                false,
                ParamObjType::Forall,
            )
            .map_err(|e| {
                WellDefinedRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "failed to define parameters in forall fact".to_string(),
                    forall_fact.line_file.clone(),
                    Some(e),
                    vec![],
                ))
            })?;

        for dom_fact in forall_fact.dom_facts.iter() {
            let mut dom_infer_result = self
                .verify_well_defined_and_store_and_infer(dom_fact.clone(), verify_state)
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
            dom_infer_result
                .relabel_all_added_facts_with_store_reason(ForallFact::premise_store_reason());
            assumption_infer_result.new_infer_result_inside(dom_infer_result);
        }
        Ok(assumption_infer_result)
    }

    /// Verify and store each `then` clause of `forall_fact` in the current environment.
    /// `by_cases_case_label`: when set, unknown `then` messages include the active `by cases` case.
    pub(crate) fn forall_verify_then_facts_in_current_env(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
        infer_result: &mut InferResult,
        assumption_infers: InferResult,
        by_cases_case_label: Option<&str>,
    ) -> Result<StmtResult, RuntimeError> {
        let mut then_verification_results: Vec<StmtResult> = Vec::new();

        let then_count = forall_fact.then_facts.len();
        let combined_atomic_then_fact = if then_count > 1 {
            let mut atomic_facts: Vec<AtomicFact> = Vec::new();
            for fact in forall_fact.then_facts.iter() {
                match fact {
                    ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                        atomic_facts.push(atomic_fact.clone());
                    }
                    _ => {
                        atomic_facts.clear();
                        break;
                    }
                }
            }
            if atomic_facts.len() == then_count {
                Some(AndFact::new(atomic_facts, forall_fact.line_file.clone()))
            } else {
                None
            }
        } else {
            None
        };
        let mut combined_atomic_then_fact_stored = false;
        for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate() {
            let mut result = self.verify_exist_or_and_chain_atomic_fact(then_fact, verify_state)?;
            if result.is_unknown() && !combined_atomic_then_fact_stored {
                if let Some(and_fact) = combined_atomic_then_fact.as_ref() {
                    let and_result = self.verify_and_fact(and_fact, verify_state)?;
                    if !and_result.is_unknown() {
                        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                            and_fact.clone().into(),
                        )?;
                        combined_atomic_then_fact_stored = true;
                        result =
                            self.verify_exist_or_and_chain_atomic_fact(then_fact, verify_state)?;
                    }
                }
            }
            if result.is_unknown() {
                let then_one_based = then_index + 1;
                let then_fact_as_fact = then_fact.clone().to_fact();
                let result = self.structured_unknown_result_for_failed_fact(
                    &then_fact_as_fact,
                    verify_state,
                    result,
                )?;
                let result = result.wrap_unknown_for_fact(then_fact_as_fact.clone());
                let child_unknown = result.as_fact_unknown().cloned();
                let detail_lines = by_cases_case_label
                    .map(|case_s| format!("by cases: under case `{}`", case_s))
                    .into_iter()
                    .collect::<Vec<_>>();
                return Ok(FactUnknown::forall_with_failed_prove(
                    forall_fact.clone(),
                    then_one_based,
                    then_count,
                    then_fact_as_fact,
                    child_unknown,
                    detail_lines,
                )
                .into());
            }

            self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                then_fact.clone(),
            )?;

            if let Some(non_factual_success) = result.non_factual_success() {
                infer_result.new_infer_result_inside(non_factual_success.infers.clone());
            } else if result.factual_success().is_some() {
                // Do not merge then-fact verification `infers` into `infer_result` (e.g. instantiated
                // `finite_set_min(S) <= a` from a known forall). Each then proof is attached as Steps under
                // `verified_by` for JSON/CLI.
            } else {
                unreachable!("stmt unknown is handled above before this match")
            }
            then_verification_results.push(result);
        }

        infer_result.add_verified_statement(&forall_fact.clone().into());
        let infer_for_success = std::mem::replace(infer_result, InferResult::new());
        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
            forall_fact.clone().into(),
            infer_for_success,
            VerifiedByResult::forall_proof(
                forall_fact.clone(),
                then_verification_results,
                assumption_infers,
            ),
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
            return Ok(StmtUnknown::new().into());
        }

        if Self::forall_has_literal_empty_obj_parameter_domain(forall_fact) {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    forall_fact.clone().into(),
                    "forall over empty parameter set".to_string(),
                    Vec::new(),
                )
                .into(),
            );
        }

        self.run_in_local_env(|rt| {
            let assumption_infer_result =
                rt.forall_assume_params_and_dom_in_current_env(forall_fact, verify_state)?;
            let mut infer_result = InferResult::new();
            rt.forall_verify_then_facts_in_current_env(
                forall_fact,
                verify_state,
                &mut infer_result,
                assumption_infer_result,
                None,
            )
        })
    }

    fn forall_has_literal_empty_obj_parameter_domain(forall_fact: &ForallFact) -> bool {
        forall_fact
            .params_def_with_type
            .groups
            .iter()
            .any(|group| match &group.param_type {
                ParamType::Obj(Obj::ListSet(list_set)) => list_set.list.is_empty(),
                ParamType::Obj(Obj::Range(range)) => integer_range_has_no_literal_points(
                    range.start.as_ref(),
                    range.end.as_ref(),
                    false,
                ),
                ParamType::Obj(Obj::ClosedRange(range)) => integer_range_has_no_literal_points(
                    range.start.as_ref(),
                    range.end.as_ref(),
                    true,
                ),
                _ => false,
            })
    }
}

/// A `forall` over a concrete empty integer range is valid without checking its body.
fn integer_range_has_no_literal_points(start: &Obj, end: &Obj, end_is_included: bool) -> bool {
    let Some(start) = start.evaluate_to_normalized_decimal_number() else {
        return false;
    };
    let Some(end) = end.evaluate_to_normalized_decimal_number() else {
        return false;
    };
    let Ok(start) = start.normalized_value.parse::<i128>() else {
        return false;
    };
    let Ok(end) = end.normalized_value.parse::<i128>() else {
        return false;
    };
    if end_is_included {
        end < start
    } else {
        end <= start
    }
}
