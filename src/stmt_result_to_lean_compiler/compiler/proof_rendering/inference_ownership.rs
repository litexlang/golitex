//! Compiler ownership of typed inference effects.

use super::super::*;

pub(in super::super) fn infer_rule_has_direct_compiler_environment_consumer(
    rule: &InferRule,
) -> bool {
    match rule {
        InferRule::NaturalMembershipImpliesNonnegative => true,
        InferRule::PositiveStandardSetMembershipImpliesPositive(rule) => {
            matches!(
                rule.source_set,
                StandardSet::NPos | StandardSet::QPos | StandardSet::RPos
            )
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(rule) => {
            matches!(
                rule.source_set,
                StandardSet::ZNeg | StandardSet::QNeg | StandardSet::RNeg
            )
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(rule) => matches!(
            rule.source_set,
            StandardSet::ZStar | StandardSet::QStar | StandardSet::RStar | StandardSet::CStar
        ),
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero
        | InferRule::StrictOrderComparedToZeroImpliesWeakOrder
        | InferRule::NumericOrderBoundImpliesZeroSign => true,
        InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => true,
        InferRule::SubsetImpliesElementwiseMembershipForall(_)
        | InferRule::SupersetImpliesElementwiseMembershipForall(_)
        | InferRule::ConjunctionImpliesComponent(_)
        | InferRule::ChainImpliesComponent(_)
        | InferRule::EqualityChainClosure(_)
        | InferRule::NumericOrderChainClosure(_)
        | InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(_)
        | InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(_) => true,
        InferRule::SetBuilderBaseMembershipProjection
        | InferRule::SetBuilderPredicateProjection { .. }
        | InferRule::FunctionRangeMembershipImpliesCodomainMembership
        | InferRule::ListSetMembershipImpliesEqualityAlternatives(_) => true,
        InferRule::DefinedPredicateParameterRequirementProjection(_)
        | InferRule::DefinedPredicateDefinitionClauseProjection(_)
        | InferRule::RegisteredTransitivePredicateChainClosure(_)
        | InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(_)
        | InferRule::CartesianMembershipProjection(_) => false,
    }
}

pub(in super::super) fn infer_result_effects_are_fully_owned_by_direct_compiler_rules(
    result: &SuccessInferResult,
) -> bool {
    let advertised = result
        .store_fact_outputs
        .iter()
        .flat_map(|output| {
            output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .filter_map(|(fact, fact_id)| fact_id.map(|fact_id| (fact_id, fact.to_string())))
        })
        .collect::<HashSet<_>>();
    let mut typed = HashSet::new();
    collect_supported_typed_infer_conclusions(result, &mut typed);
    typed.retain(|conclusion| advertised.contains(conclusion));
    advertised == typed
}

pub(in super::super) fn collect_supported_typed_infer_conclusions(
    result: &SuccessInferResult,
    conclusions: &mut HashSet<(FactId, String)>,
) {
    for application in &result.rule_applications {
        if !infer_rule_has_direct_compiler_environment_consumer(&application.rule) {
            continue;
        }
        for conclusion in &application.conclusions {
            if let Some(fact_id) = conclusion.fact_id {
                conclusions.insert((fact_id, conclusion.fact.to_string()));
            }
            collect_supported_typed_infer_conclusions(&conclusion.infers, conclusions);
        }
    }
}
