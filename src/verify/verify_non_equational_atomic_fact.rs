use crate::prelude::*;
use crate::verify::verify_builtin_rules::{
    builtin_in_fact_result_for_evaluated_number_in_standard_set,
    builtin_not_in_fact_result_for_evaluated_number_in_standard_set,
};

impl Runtime {
    pub(crate) fn verify_non_equational_atomic_fact_with_direct_routes(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        let leaf_result =
            self.verify_non_equational_atomic_fact_with_known_fact_then_computation(atomic_fact)?;
        if leaf_result.is_true() {
            return Ok(leaf_result);
        }

        let builtin_state = UseBuiltinRuleVerifyState::new();
        self.verify_non_equational_atomic_fact_with_one_builtin_rule(atomic_fact, &builtin_state)
    }

    pub(crate) fn verify_non_equational_atomic_fact_with_known_fact(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        let result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(atomic_fact)?;
        Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result))
    }

    pub(crate) fn verify_non_equational_atomic_fact_with_known_fact_then_computation(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_non_equational_atomic_fact_with_known_fact(atomic_fact)?;
        if known_result.is_true() {
            return Ok(known_result);
        }

        let result = self.verify_non_equational_atomic_fact_by_builtin_computation(atomic_fact);
        if result.is_true() {
            return Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result));
        }

        let Some((definition_resolved_fact, equality_transport)) =
            self.atomic_fact_with_explicit_definitions_resolved(atomic_fact)?
        else {
            return Ok(result);
        };
        let resolved_fact = match &definition_resolved_fact {
            AtomicFact::InFact(fact) => fact
                .element
                .evaluate_to_normalized_decimal_number()
                .map(|number| {
                    InFact::new(number.into(), fact.set.clone(), fact.line_file.clone()).into()
                })
                .unwrap_or_else(|| definition_resolved_fact.clone()),
            AtomicFact::NotInFact(fact) => fact
                .element
                .evaluate_to_normalized_decimal_number()
                .map(|number| {
                    NotInFact::new(number.into(), fact.set.clone(), fact.line_file.clone()).into()
                })
                .unwrap_or_else(|| definition_resolved_fact.clone()),
            _ => definition_resolved_fact.clone(),
        };
        let resolved_result =
            self.verify_non_equational_atomic_fact_by_builtin_computation(&resolved_fact);
        if !resolved_result.is_true() {
            return Ok(result);
        }

        let expected_target: Fact = atomic_fact.clone().into();
        let resolved_target: Fact = resolved_fact.clone().into();
        let definition_resolved_target: Fact = definition_resolved_fact.into();
        let mut transformation_steps = Vec::new();
        if resolved_target.to_string() != definition_resolved_target.to_string() {
            transformation_steps.push(FactTransformationStep::new(
                definition_resolved_target,
                FactTransformationRule::RationalNormalization,
            ));
        }
        transformation_steps.push(FactTransformationStep::new(
            expected_target.clone(),
            FactTransformationRule::EqualityRewrite(equality_transport),
        ));
        let fact_transformation =
            FactTransformationEvidence::new(resolved_target.clone(), transformation_steps);
        let result = FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            expected_target.clone(),
            "builtin computation after explicit object definition resolution".to_string(),
            BuiltinRuleEvidence::ResolvedAtomicFactComputation(
                ResolvedAtomicFactComputationBuiltinRuleEvidence::new(
                    expected_target,
                    resolved_target,
                    fact_transformation,
                ),
            ),
            vec![resolved_result],
        )
        .into();
        Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result))
    }

    pub(crate) fn verify_non_equational_atomic_fact_by_builtin_computation(
        &self,
        atomic_fact: &AtomicFact,
    ) -> StmtResult {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        match atomic_fact {
            AtomicFact::InFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return StmtUnknown::new().into();
                };
                let Some(number) = fact.element.evaluate_to_normalized_decimal_number() else {
                    return StmtUnknown::new().into();
                };
                builtin_in_fact_result_for_evaluated_number_in_standard_set(fact, &number, set)
            }
            AtomicFact::NotInFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return StmtUnknown::new().into();
                };
                let Some(number) = fact.element.evaluate_to_normalized_decimal_number() else {
                    return StmtUnknown::new().into();
                };
                builtin_not_in_fact_result_for_evaluated_number_in_standard_set(fact, &number, set)
            }
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                if self.verify_number_comparison_builtin_rule(atomic_fact) != Some(true) {
                    return StmtUnknown::new().into();
                }
                FactualStmtSuccess::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "number comparison".to_string(),
                    BuiltinRuleEvidence::ClosedNumericComparison(
                        ClosedNumericComparisonBuiltinRuleEvidence::new(atomic_fact.clone().into()),
                    ),
                    Vec::new(),
                )
                .into()
            }
            AtomicFact::NotEqualFact(fact) => self
                .verify_resolved_numeric_not_equal_without_builtin_recursion(fact)
                .unwrap_or_else(|| StmtUnknown::new().into()),
            AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_) => {
                let prime_result = self.verify_prime_fact_by_computation(atomic_fact);
                if prime_result.is_unknown() {
                    self.verify_coprime_fact_by_computation(atomic_fact)
                } else {
                    prime_result
                }
            }
            AtomicFact::EqualFact(_) => {
                unreachable!("equality has an owner-specific computation route")
            }
            _ => StmtUnknown::new().into(),
        }
    }

    pub(crate) fn verify_non_equational_atomic_fact_with_one_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        if !builtin_state.can_apply_builtin_rule() {
            return Ok(StmtUnknown::new().into());
        }
        let child_state = builtin_state.after_applying_builtin_rule();
        if let Some(result) = self.try_verify_atomic_fact_with_local_builtin_catalog(atomic_fact)? {
            return Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result));
        }
        if let Some(result) =
            self.try_verify_atomic_fact_from_known_set_builder_membership(atomic_fact)?
        {
            return Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result));
        }
        let result = self.verify_non_equational_atomic_fact_with_builtin_rules_inner(
            atomic_fact,
            &child_state,
        )?;
        Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result))
    }

    pub fn verify_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
        post_process: bool,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result = self.verify_non_equational_atomic_fact_with_direct_routes(atomic_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_atomic_fact_with_builtin_strategy(atomic_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();

            if let Some(verified_by_definition) = self
                .verify_atomic_fact_using_builtin_or_prop_definition(
                    atomic_fact,
                    &verify_state_add_one_round,
                )?
            {
                return Ok(verified_by_definition);
            }

            result = self.verify_non_equational_atomic_fact_with_known_forall(
                atomic_fact,
                &verify_state_add_one_round,
            )?;
            if result.is_true() {
                return Ok(result);
            }

            result = self.verify_non_equational_atomic_fact_with_strategy(
                atomic_fact,
                &verify_state_add_one_round,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        if post_process {
            result =
                self.post_process_non_equational_atomic_fact(atomic_fact, verify_state, result)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    // If direct verification failed, try order-dual, then registered user-defined prop properties.
    fn post_process_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let result = self.builtin_post_process_non_equational_atomic_fact(
            atomic_fact,
            verify_state,
            result,
        )?;
        if result.is_true() {
            return Ok(result);
        }
        let result = self.use_known_reflexive_prop(atomic_fact, result)?;
        if result.is_true() {
            return Ok(result);
        }
        self.use_known_symmetric_prop(atomic_fact, verify_state, result)
    }

    fn builtin_post_process_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let transposed_fact = match atomic_fact {
            // Direct known not-equality symmetry is owned by the builtin rule.
            // Keep this full-verifier fallback so a reversed known `forall`
            // conclusion remains available after the bounded builtin attempt.
            AtomicFact::NotEqualFact(fact) => NotEqualFact::new(
                fact.right.clone(),
                fact.left.clone(),
                fact.line_file.clone(),
            )
            .into(),
            _ => {
                let Some(transposed) = atomic_fact.transposed_binary_order_equivalent() else {
                    return Ok(result);
                };
                transposed
            }
        };
        let transposed_result =
            self.verify_non_equational_atomic_fact(&transposed_fact, verify_state, false)?;
        Self::wrap_post_process_alternate_fact_result(atomic_fact, transposed_result, result)
    }

    fn use_known_reflexive_prop(
        &mut self,
        atomic_fact: &AtomicFact,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let AtomicFact::NormalAtomicFact(f) = atomic_fact else {
            return Ok(result);
        };
        if f.body.len() != 2 {
            return Ok(result);
        }
        if f.body[0].to_string() != f.body[1].to_string() {
            return Ok(result);
        }
        let prop_name = f.predicate.to_string();
        for env in self.iter_environments_from_top() {
            if env.known_reflexive_props.contains_key(&prop_name) {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "registered reflexive prop".to_string(),
                        Vec::new(),
                    )
                    .into(),
                );
            }
        }
        Ok(result)
    }

    fn use_known_symmetric_prop(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let AtomicFact::NormalAtomicFact(f) = atomic_fact else {
            return Ok(result);
        };
        if f.body.len() < 2 {
            return Ok(result);
        }
        let prop_name = f.predicate.to_string();

        let mut permutations: Vec<Vec<usize>> = Vec::new();
        for env in self.iter_environments_from_top() {
            if let Some(perms) = env.known_symmetric_props.get(&prop_name) {
                for g in perms {
                    if g.len() == f.body.len() {
                        permutations.push(g.clone());
                    }
                }
            }
        }

        for gather in permutations {
            let Some(alt) = atomic_fact.symmetric_reordered_args(&gather) else {
                continue;
            };
            let alt_result = self.verify_non_equational_atomic_fact(&alt, verify_state, false)?;
            if alt_result.is_true() {
                return Self::wrap_post_process_alternate_fact_result(
                    atomic_fact,
                    alt_result,
                    result,
                );
            }
        }

        Ok(result)
    }

    fn wrap_post_process_alternate_fact_result(
        original: &AtomicFact,
        alternate_result: StmtResult,
        fallback: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        match alternate_result {
            StmtResult::Fact(fact_result) => {
                let Some(inner_success) = (*fact_result).into_success() else {
                    return Ok(fallback);
                };
                let FactualStmtSuccess {
                    verified_by,
                    infers: _,
                    stmt: _,
                    ..
                } = inner_success;
                Ok(FactualStmtSuccess::new_with_verified_by_known_fact(
                    original.clone().into(),
                    verified_by,
                    Vec::new(),
                )
                .into())
            }
            other if other.is_true() => Ok(other),
            _ => Ok(fallback),
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn anonymous_function_membership_is_not_dispatched_by_the_generic_orchestrator() {
        let source = include_str!("verify_non_equational_atomic_fact.rs");
        let implementation = source.split("#[cfg(test)]").next().unwrap_or(source);

        assert!(!implementation.contains("Obj::AnonymousFn"));
        assert!(!implementation.contains("verify_in_fact_anonymous_fn_signature_matches_fn_set"));
    }
}
