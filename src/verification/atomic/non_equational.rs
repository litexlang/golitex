//! Verification for non-equational atomic predicates.

use crate::error::RuntimeError;
use crate::fact::{AtomicFact, Fact, NotEqualFact};
use crate::inference::SuccessInferResult;
use crate::object::Obj;
use crate::result::{
    BuiltinRuleEvidence, RegisteredReflexivePredicateBuiltinRuleEvidence,
    RegisteredSymmetricPredicateBuiltinRuleEvidence, StmtResult, SuccessFactStmtResult,
    SuccessStmtResult, UnknownGenericStmtResult,
};
use crate::runtime::Runtime;
use crate::verification::builtin_rules::{
    builtin_in_fact_result_for_evaluation_in_standard_set,
    builtin_not_in_fact_result_for_evaluation_in_standard_set,
};
use crate::verification::{BuiltinRuleSearchState, VerifyState};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AlternateFactSearch {
    Enabled,
    Disabled,
}

impl Runtime {
    pub fn verify_non_equational_atomic_fact_with_bounded_builtin_routes(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        let zero_premise_result =
            self.verify_non_equational_atomic_fact_with_zero_premise_verification(atomic_fact)?;
        if zero_premise_result.is_success() {
            return Ok(zero_premise_result);
        }

        let builtin_state = BuiltinRuleSearchState::initial();
        self.verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule(
            atomic_fact,
            &builtin_state,
        )
    }

    // A premise is a child fact that a rule must verify before concluding its parent fact.
    // Zero-premise verification closes the current fact without generating such child facts:
    // it first reuses a known fact, then tries direct evaluation on the fact as written.
    // This extra phase is necessary for `x * 2 >= 0` from known `x >= 0`: the multiplication
    // rule consumes the allowed builtin-rule step, while its closed premise `2 >= 0` must still
    // be evaluated without opening another premise-producing rule step.
    pub fn verify_non_equational_atomic_fact_with_zero_premise_verification(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(atomic_fact)?;
        if known_result.is_success() {
            return Ok(known_result);
        }

        let result = self.verify_non_equational_atomic_fact_by_direct_evaluation(atomic_fact);
        Ok(self.cache_successful_atomic_fact_for_statement(atomic_fact, result))
    }

    // Direct evaluation is the computation arm of zero-premise verification: it may inspect
    // the current expression, but it cannot generate premises or apply another rule.
    pub fn verify_non_equational_atomic_fact_by_direct_evaluation(
        &self,
        atomic_fact: &AtomicFact,
    ) -> StmtResult {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        match atomic_fact {
            AtomicFact::InFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return UnknownGenericStmtResult::new().into();
                };
                let Some(evaluation) = fact
                    .element
                    .evaluate_to_normalized_decimal_number_with_result()
                else {
                    return UnknownGenericStmtResult::new().into();
                };
                builtin_in_fact_result_for_evaluation_in_standard_set(fact, &evaluation, set)
            }
            AtomicFact::NotInFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return UnknownGenericStmtResult::new().into();
                };
                let Some(evaluation) = fact
                    .element
                    .evaluate_to_normalized_decimal_number_with_result()
                else {
                    return UnknownGenericStmtResult::new().into();
                };
                builtin_not_in_fact_result_for_evaluation_in_standard_set(fact, &evaluation, set)
            }
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                let Some(evidence) = self.verify_number_comparison_builtin_rule(atomic_fact) else {
                    return UnknownGenericStmtResult::new().into();
                };
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "number comparison".to_string(),
                    evidence,
                    Vec::new(),
                )
                .into()
            }
            AtomicFact::NotEqualFact(fact) => self
                .verify_resolved_numeric_not_equal_without_builtin_recursion(fact)
                .unwrap_or_else(|| UnknownGenericStmtResult::new().into()),
            AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_) => {
                let prime_result = self.verify_prime_fact_by_computation(atomic_fact);
                if prime_result.is_unknown() {
                    self.verify_coprime_fact_by_computation(atomic_fact)
                } else {
                    prime_result
                }
            }
            AtomicFact::EqualFact(_) => {
                unreachable!("equality has an owner-specific direct-evaluation route")
            }
            _ => UnknownGenericStmtResult::new().into(),
        }
    }

    // This bounded phase may generate premises, so entering it consumes the available
    // builtin-rule step before any child fact is checked.
    pub fn verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        if !builtin_state.can_apply_rule() {
            return Ok(UnknownGenericStmtResult::new().into());
        }
        let child_state = builtin_state.after_applying_rule();
        if let Some(result) =
            self.try_verify_atomic_fact_from_known_set_builder_membership(atomic_fact)?
        {
            return Ok(self.cache_successful_atomic_fact_for_statement(atomic_fact, result));
        }
        let result = self.verify_non_equational_atomic_fact_with_builtin_rules_inner(
            atomic_fact,
            &child_state,
        )?;
        Ok(self.cache_successful_atomic_fact_for_statement(atomic_fact, result))
    }

    pub fn verify_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        alternate_fact_search: AlternateFactSearch,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result =
            self.verify_non_equational_atomic_fact_with_bounded_builtin_routes(atomic_fact)?;
        if result.is_success() {
            return Ok(result);
        }

        result = self.verify_atomic_fact_with_builtin_strategy(atomic_fact)?;
        if result.is_success() {
            return Ok(result);
        }

        if verify_state.is_initial_round() {
            let next_round_state = verify_state.with_next_round();

            if let Some(verified_by_definition) = self
                .verify_atomic_fact_using_builtin_or_prop_definition(
                    atomic_fact,
                    &next_round_state,
                )?
            {
                return Ok(verified_by_definition);
            }

            result = self.verify_non_equational_atomic_fact_with_known_forall(
                atomic_fact,
                &next_round_state,
            )?;
            if result.is_success() {
                return Ok(result);
            }
        }

        if alternate_fact_search == AlternateFactSearch::Enabled {
            result =
                self.post_process_non_equational_atomic_fact(atomic_fact, verify_state, result)?;
            if result.is_success() {
                return Ok(result);
            }
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }

    // If direct verification failed, try order-dual, then registered user-defined prop properties.
    fn post_process_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let result = self.builtin_post_process_non_equational_atomic_fact(
            atomic_fact,
            verify_state,
            result,
        )?;
        if result.is_success() {
            return Ok(result);
        }
        let result = self.use_known_reflexive_prop(atomic_fact, result)?;
        if result.is_success() {
            return Ok(result);
        }
        self.use_known_symmetric_prop(atomic_fact, verify_state, result)
    }

    fn builtin_post_process_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
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
        let transposed_result = self.verify_non_equational_atomic_fact(
            &transposed_fact,
            verify_state,
            AlternateFactSearch::Disabled,
        )?;
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
            if env.predicate_algebraic_properties.is_reflexive(&prop_name) {
                let target: Fact = atomic_fact.clone().into();
                return Ok(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        target.clone(),
                        "registered reflexive prop".to_string(),
                        BuiltinRuleEvidence::RegisteredReflexivePredicate(
                            RegisteredReflexivePredicateBuiltinRuleEvidence::new(
                                target,
                                prop_name,
                            ),
                        ),
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
        verify_state: &VerifyState,
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
            if let Some(perms) = env
                .predicate_algebraic_properties
                .symmetric_argument_permutations(&prop_name)
            {
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
            let alt_result = self.verify_non_equational_atomic_fact(
                &alt,
                verify_state,
                AlternateFactSearch::Disabled,
            )?;
            if alt_result.is_success() {
                return Ok(Self::wrap_registered_symmetric_prop_result(
                    atomic_fact,
                    prop_name,
                    gather,
                    alt,
                    alt_result,
                ));
            }
        }

        Ok(result)
    }

    /// `Wrap`: retain the exact reordered child Result and the permutation
    /// selected by the registered predicate property. Verification owns the
    /// child; this layer only records how it is lifted to the requested target.
    fn wrap_registered_symmetric_prop_result(
        target: &AtomicFact,
        predicate_name: String,
        gather: Vec<usize>,
        alternate: AtomicFact,
        alternate_result: StmtResult,
    ) -> StmtResult {
        debug_assert!(alternate_result.is_success());
        let target: Fact = target.clone().into();
        let alternate: Fact = alternate.into();
        SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            target.clone(),
            "registered symmetric prop".to_string(),
            BuiltinRuleEvidence::RegisteredSymmetricPredicate(
                RegisteredSymmetricPredicateBuiltinRuleEvidence::new(
                    target,
                    predicate_name,
                    gather,
                    alternate,
                ),
            ),
            vec![alternate_result],
        )
        .into()
    }

    fn wrap_post_process_alternate_fact_result(
        original: &AtomicFact,
        alternate_result: StmtResult,
        fallback: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        match alternate_result {
            StmtResult::Success(SuccessStmtResult::Fact(inner_success)) => {
                Ok(SuccessFactStmtResult::new_with_statement_proof_cache(
                    original.clone().into(),
                    SuccessInferResult::new(),
                    inner_success.verification,
                )
                .into())
            }
            other if other.is_success() => Ok(other),
            _ => Ok(fallback),
        }
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/verification/atomic/non_equational.rs"]
mod tests;
