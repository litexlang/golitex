use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InferRule {
    NaturalMembershipImpliesNonnegative,
    PositiveStandardSetMembershipImpliesPositive(
        PositiveStandardSetMembershipImpliesPositiveInferRule,
    ),
    NegativeStandardSetMembershipImpliesNegative(
        NegativeStandardSetMembershipImpliesNegativeInferRule,
    ),
    NonzeroStandardSetMembershipImpliesNonzero(NonzeroStandardSetMembershipImpliesNonzeroInferRule),
    SetBuilderBaseMembershipProjection,
    SetBuilderPredicateProjection {
        clause_index: usize,
    },
    DefinedPredicateParameterRequirementProjection(
        DefinedPredicateParameterRequirementProjectionInferRule,
    ),
    DefinedPredicateDefinitionClauseProjection(DefinedPredicateDefinitionClauseProjectionInferRule),
    EqualityChainClosure(EqualityChainClosureInferRule),
    NumericOrderChainClosure(NumericOrderChainClosureInferRule),
    ClosedPositivePowerEqualityImpliesEqualSideMembership(
        ClosedPositivePowerEqualityImpliesEqualSideMembershipInferRule,
    ),
    PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(
        PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembershipInferRule,
    ),
    RegisteredTransitivePredicateChainClosure(RegisteredTransitivePredicateChainClosureInferRule),
    TupleEqualityWithKnownTupleImpliesTupleShape(
        TupleEqualityWithKnownTupleImpliesTupleShapeInferRule,
    ),
    CartesianMembershipProjection(CartesianMembershipProjectionInferRule),
    ListSetMembershipImpliesEqualityAlternatives(
        ListSetMembershipImpliesEqualityAlternativesInferRule,
    ),
    NumericOrderBoundImpliesZeroSign,
    MultiplicationByNegativeOneReversesOrderAgainstZero,
    StrictOrderComparedToZeroImpliesWeakOrder,
    MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(
        MembershipInSetWithKnownEqualityImpliesMembershipInEqualSetInferRule,
    ),
    SubsetImpliesElementwiseMembershipForall(SubsetImpliesElementwiseMembershipForallInferRule),
    SupersetImpliesElementwiseMembershipForall(SupersetImpliesElementwiseMembershipForallInferRule),
    ConjunctionImpliesComponent(ConjunctionImpliesComponentInferRule),
}
