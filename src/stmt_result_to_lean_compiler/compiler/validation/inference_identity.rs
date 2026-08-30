//! Inference identities, rule names, and semantic structure.

use super::super::*;

pub(in super::super) fn exact_ordered_fact_ids_from_store_results(
    infer_result: &SuccessInferResult,
    expected_facts: &[Fact],
    statement_family: &str,
) -> Result<Vec<FactId>, String> {
    if infer_result.store_fact_outputs.len() != expected_facts.len() {
        return Err(format!(
            "{statement_family} stored {} facts but its Result requires {}",
            infer_result.store_fact_outputs.len(),
            expected_facts.len()
        ));
    }
    infer_result
        .store_fact_outputs
        .iter()
        .zip(expected_facts.iter())
        .enumerate()
        .map(|(index, (stored, expected))| {
            if !frozen_result_facts_align(&stored.itself_and_why_itself_is_stored.0, expected) {
                return Err(format!(
                    "{statement_family} store {index} changed `{expected}` to `{}`",
                    stored.itself_and_why_itself_is_stored.0
                ));
            }
            stored.fact_id.ok_or_else(|| {
                format!("{statement_family} store {index} for `{expected}` has no FactId")
            })
        })
        .collect()
}

pub(in super::super) fn infer_result_retains_fact_id(
    infer_result: &SuccessInferResult,
    expected_fact: &Fact,
    expected_fact_id: FactId,
) -> bool {
    infer_result.store_fact_outputs.iter().any(|output| {
        (output.fact_id == Some(expected_fact_id)
            && frozen_result_facts_align(&output.itself_and_why_itself_is_stored.0, expected_fact))
            || output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .any(|(fact, fact_id)| {
                    frozen_result_facts_align(fact, expected_fact)
                        && *fact_id == Some(expected_fact_id)
                })
    })
}

pub(in super::super) fn frozen_result_facts_align(left: &Fact, right: &Fact) -> bool {
    left.to_string() == right.to_string()
        || membership_facts_are_equal_up_to_nested_binder_alpha(left, right)
        || equality_facts_are_equal_up_to_nested_binder_alpha(left, right)
}

pub(in super::super) fn defined_predicate_infer_rule(rule: &InferRule) -> bool {
    matches!(
        rule,
        InferRule::DefinedPredicateParameterRequirementProjection(_)
            | InferRule::DefinedPredicateDefinitionClauseProjection(_)
    )
}

pub(in super::super) fn infer_rule_name(rule: &InferRule) -> &'static str {
    match rule {
        InferRule::NaturalMembershipImpliesNonnegative => "NaturalMembershipImpliesNonnegative",
        InferRule::PositiveStandardSetMembershipImpliesPositive(_) => {
            "PositiveStandardSetMembershipImpliesPositive"
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(_) => {
            "NegativeStandardSetMembershipImpliesNegative"
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(_) => {
            "NonzeroStandardSetMembershipImpliesNonzero"
        }
        InferRule::SetBuilderBaseMembershipProjection => "SetBuilderBaseMembershipProjection",
        InferRule::SetBuilderPredicateProjection { .. } => "SetBuilderPredicateProjection",
        InferRule::DefinedPredicateParameterRequirementProjection(_) => {
            "DefinedPredicateParameterRequirementProjection"
        }
        InferRule::DefinedPredicateDefinitionClauseProjection(_) => {
            "DefinedPredicateDefinitionClauseProjection"
        }
        InferRule::EqualityChainClosure(_) => "EqualityChainClosure",
        InferRule::NumericOrderChainClosure(_) => "NumericOrderChainClosure",
        InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(_) => {
            "ClosedPositivePowerEqualityImpliesEqualSideMembership"
        }
        InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(_) => {
            "PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership"
        }
        InferRule::RegisteredTransitivePredicateChainClosure(_) => {
            "RegisteredTransitivePredicateChainClosure"
        }
        InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(_) => {
            "TupleEqualityWithKnownTupleImpliesTupleShape"
        }
        InferRule::CartesianMembershipProjection(_) => "CartesianMembershipProjection",
        InferRule::ListSetMembershipImpliesEqualityAlternatives(_) => {
            "ListSetMembershipImpliesEqualityAlternatives"
        }
        InferRule::FunctionRangeMembershipImpliesCodomainMembership => {
            "FunctionRangeMembershipImpliesCodomainMembership"
        }
        InferRule::NumericOrderBoundImpliesZeroSign => "NumericOrderBoundImpliesZeroSign",
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
            "MultiplicationByNegativeOneReversesOrderAgainstZero"
        }
        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
            "StrictOrderComparedToZeroImpliesWeakOrder"
        }
        InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => {
            "MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet"
        }
        InferRule::SubsetImpliesElementwiseMembershipForall(_) => {
            "SubsetImpliesElementwiseMembershipForall"
        }
        InferRule::SupersetImpliesElementwiseMembershipForall(_) => {
            "SupersetImpliesElementwiseMembershipForall"
        }
        InferRule::ConjunctionImpliesComponent(_) => "ConjunctionImpliesComponent",
    }
}

pub(in super::super) fn validate_flattened_inferred_fact_ids_are_visible(
    infer_result: &SuccessInferResult,
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
    result_layer: &str,
) -> Result<(), String> {
    for (store_index, output) in infer_result.store_fact_outputs.iter().enumerate() {
        let fact_id = output
            .fact_id
            .ok_or_else(|| format!("{result_layer} store {store_index} has no frozen FactId"))?;
        resolve_fact_citation(
            &fact_id,
            &output.itself_and_why_itself_is_stored.0,
            environment_stack,
        )?;
        if output.inferred_facts.len() != output.inferred_fact_ids.len() {
            return Err(format!(
                "{result_layer} store {store_index} changed its inferred FactId arity"
            ));
        }
        for (inferred_index, (fact, fact_id)) in output
            .inferred_facts
            .iter()
            .zip(output.inferred_fact_ids.iter())
            .enumerate()
        {
            let fact_id = fact_id.ok_or_else(|| {
                format!(
                    "{result_layer} store {store_index} inferred fact {inferred_index} has no frozen FactId"
                )
            })?;
            resolve_fact_citation(&fact_id, fact, environment_stack)?;
        }
    }
    Ok(())
}

pub(in super::super) fn success_infer_results_have_same_semantic_structure(
    left: &SuccessInferResult,
    right: &SuccessInferResult,
) -> bool {
    success_infer_results_have_same_structure(left, right, true)
}

pub(in super::super) fn success_infer_results_have_same_structure(
    left: &SuccessInferResult,
    right: &SuccessInferResult,
    compare_store_reasons: bool,
) -> bool {
    left.store_fact_outputs.len() == right.store_fact_outputs.len()
        && left
            .store_fact_outputs
            .iter()
            .zip(right.store_fact_outputs.iter())
            .all(|(left, right)| {
                left.fact_id == right.fact_id
                    && left.itself_and_why_itself_is_stored.0.to_string()
                        == right.itself_and_why_itself_is_stored.0.to_string()
                    && (!compare_store_reasons
                        || left.itself_and_why_itself_is_stored.1
                            == right.itself_and_why_itself_is_stored.1)
                    && left.inferred_fact_ids == right.inferred_fact_ids
                    && left.inferred_facts.len() == right.inferred_facts.len()
                    && left
                        .inferred_facts
                        .iter()
                        .zip(right.inferred_facts.iter())
                        .all(|(left, right)| left.to_string() == right.to_string())
            })
        && left.rule_applications.len() == right.rule_applications.len()
        && left
            .rule_applications
            .iter()
            .zip(right.rule_applications.iter())
            .all(|(left, right)| {
                left.rule == right.rule
                    && left.premises.len() == right.premises.len()
                    && left
                        .premises
                        .iter()
                        .zip(right.premises.iter())
                        .all(|(left, right)| {
                            left.fact_id == right.fact_id
                                && left.fact.to_string() == right.fact.to_string()
                        })
                    && left.conclusions.len() == right.conclusions.len()
                    && left
                        .conclusions
                        .iter()
                        .zip(right.conclusions.iter())
                        .all(|(left, right)| {
                            left.fact_id == right.fact_id
                                && left.fact.to_string() == right.fact.to_string()
                                && success_infer_results_have_same_structure(
                                    &left.infers,
                                    &right.infers,
                                    compare_store_reasons,
                                )
                        })
            })
}

pub(in super::super) fn equality_transport_has_no_steps(
    transport: Option<&EqualityTransportEvidence>,
) -> bool {
    transport.is_none_or(|transport| transport.steps.is_empty())
}

pub(in super::super) fn atomic_fact_is_logically_negated(fact: &AtomicFact) -> bool {
    matches!(
        fact,
        AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::NotEqualFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::NotIsCartFact(_)
            | AtomicFact::NotIsTupleFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
    )
}
