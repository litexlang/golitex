//! Typed evidence emitted by builtin verification rules.

use crate::prelude::*;
use std::fmt;

/// Stable identities for builtin verifier producers that are not in the
/// reviewed ToLean catalog. These rules are still fully typed in Rust;
/// the Lean backend must reject them by exact rule ID until an explicit
/// mapping is reviewed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UncataloguedBuiltinRule {
    ComplexEqualityResultWithSteps,
    ComplexOrderResult,
    DecompositionParts,
    ExecBuiltinThmStmtImpl,
    ExecuteTrustedFact,
    FactualEqualSuccessByBuiltinReasonWithSubgoals,
    FnSetEqualityVerifiedByBuiltinRulesResult,
    IndexedFamilySubsetSuccess,
    MaybeVerifyInFactFiniteSetExtremum,
    MaybeVerifyInFactInUnfoldedUserDefinedSetOnce,
    NativeEqualSuccess,
    NotInFactVerifiedByBuiltinRulesResult,
    NumberInSetVerifiedByBuiltinRulesResult,
    NumberInSetVerifiedByBuiltinRulesResultWithSubgoals,
    PythagoreanCoreResult,
    SetEqualitySuccess,
    TestFixture,
    TrigCoreDependencyResults,
    TryAbsLeFromEvenPowerLe,
    TryBaseLeFromPowLeSamePositiveIntegerExponentNonnegativeBase,
    TryBaseLeFromPowLeSamePositiveRealExponentPositiveBase,
    TryBaseLtFromPowLtSamePositiveRealExponentPositiveBase,
    TryLessAlgebra,
    TryLessEqualAlgebra,
    TryLessEqualFiniteSetSumPointwiseOnSameSet,
    TryLessEqualFiniteSetSummandNonnegativeSum,
    TryLessEqualFromPositiveDenominatorBound,
    TryLessEqualFromPositiveDivisionProductBound,
    TryMulLeComponentwiseNonnegativeFactors,
    TryMulLeSharedLeft,
    TryMulLeZeroByWeakSigns,
    TryMulLtSharedLeft,
    TryMulLtZeroBySigns,
    TryPowLeEvenExponentFromAbsLe,
    TryPowLeSameNegativeIntegerExponentPositiveBaseReversesOrder,
    TryPowLeSamePositiveIntegerExponentNonnegativeBase,
    TryPowLeSamePositiveOddIntegerExponent,
    TryPowLeZeroOddExponentFromNonpositiveBase,
    TryPowLtEvenExponentFromAbsLt,
    TryPowLtSamePositiveIntegerExponentNonnegativeBase,
    TryPowLtSamePositiveOddIntegerExponent,
    TryPowLtSamePositiveRealExponentPositiveBase,
    TryPowLtZeroOddExponentFromNegativeBase,
    TryTrigQuotientDefinition,
    TryVerifyAbsFiniteSetSumTriangle,
    TryVerifyAbsFiniteSumTriangle,
    TryVerifyAbsLowerBoundFromAbsCompare,
    TryVerifyAbsNotEqualZeroFromArgNonzero,
    TryVerifyAbsUpperBound,
    TryVerifyAddNotEqualZeroFromOperandNotEqualNegation,
    TryVerifyArcsinInverseEquality,
    TryVerifyArcsinPrincipalRange,
    TryVerifyAtomicFactFromKnownSetBuilderMembership,
    TryVerifyCartEqualityFromDimAndProjections,
    TryVerifyComponentNonzeroOrFromKnownSquareSumNotEqualZero,
    TryVerifyDivNotEqualZeroFromNumeratorNonzero,
    TryVerifyDivisionFromKnownProduct,
    TryVerifyEmptyFiniteSetFromSizeZero,
    TryVerifyEmptySetEqualityFromNotNonempty,
    TryVerifyEqualityFromTwoSidedWeakOrder,
    TryVerifyFiniteCodomainFromKnownSurjection,
    TryVerifyFiniteNonemptySetSizeAtLeastOne,
    TryVerifyFiniteSetExtremaOrderBuiltinRule,
    TryVerifyFiniteSetProductPointwiseEquality,
    TryVerifyFiniteSetSizeCodomainLeDomainFromKnownSurjection,
    TryVerifyFiniteSetSizeFnRangeFromKnownInjection,
    TryVerifyFiniteSetSizeFromKnownBijection,
    TryVerifyFiniteSetSizeIntegerRangeEquality,
    TryVerifyFiniteSetSizeNonnegative,
    TryVerifyFiniteSetSizePartitionEquality,
    TryVerifyFiniteSetSizeSetMinusEquality,
    TryVerifyFiniteSetSizeSetMinusOfSubsetEquality,
    TryVerifyFiniteSetSizeSubsetLe,
    TryVerifyFiniteSetSizeUnionEquality,
    TryVerifyFiniteSetSizeUnionLeSum,
    TryVerifyFiniteSetSumSubstitution,
    TryVerifyInFactBySymbolicCart,
    TryVerifyIndexedSetFamilyEqualities,
    TryVerifyIntegerDiscreteSplitOrBuiltinRule,
    TryVerifyIntegerSingletonIntervalEqualityBuiltinRule,
    TryVerifyIntegerSuccessorPredecessorBuiltinRule,
    TryVerifyIntegerSuccessorTailOrFromLowerBound,
    TryVerifyIntrinsicallyPositiveNativeValueNonzero,
    TryVerifyLiteralSetIntersectionFilter,
    TryVerifyMinusOneOddNaturalPower,
    TryVerifyModDividendMinusRemainderEqualsZero,
    TryVerifyModEqRemainderFromEuclideanDivision,
    TryVerifyModRemainderBounds,
    TryVerifyNativeComplexAbsNonzero,
    TryVerifyNativeExpLnMonotonicity,
    TryVerifyNativeExpSignFactorialOrder,
    TryVerifyNativeFactorialMonotonicity,
    TryVerifyNativeINonzero,
    TryVerifyNativeLcmBasicEquality,
    TryVerifyNativeLcmGcdProductEquality,
    TryVerifyNativeLcmLeCommonPositiveMultiple,
    TryVerifyNativeRealConstantNonzero,
    TryVerifyNativeRealConstantPositive,
    TryVerifyNativeRoundingAlgebraEquality,
    TryVerifyNativeRoundingExtremaMonotonicity,
    TryVerifyNativeRoundingExtremaOrder,
    TryVerifyNativeRoundingIntegerEquality,
    TryVerifyNativeSignMonotonicity,
    TryVerifyNativeSignNonzeroCharacterization,
    TryVerifyNonemptyFiniteSetFromPositiveFiniteSetSize,
    TryVerifyNotEqualEmptySetFromNonempty,
    TryVerifyNotEqualFactWhenZeroAndBinaryArithmeticReducesByOperandFacts,
    TryVerifyNotEqualFromKnownPositiveLowerBound,
    TryVerifyNotEqualFromKnownStrictOrder,
    TryVerifyNotEqualFromMembershipContradiction,
    TryVerifyNotEqualPowFromBaseNonzero,
    TryVerifyNotEqualZeroFromNAndOneLe,
    TryVerifyNumericLowerBoundFromKnownLowerBound,
    TryVerifyNumericUpperBoundFromKnownUpperBound,
    TryVerifyOneModEqualsOneForModulusAtLeastTwo,
    TryVerifyOneSubtractionFromKnownAddition,
    TryVerifyOperandNotEqualFromSubNotEqualZero,
    TryVerifyOperandNotEqualNegationFromAddNotEqualZero,
    TryVerifyOrByClassicalImplication,
    TryVerifyOrderNonnegativeFromMembershipInN,
    TryVerifyOrderOneLeFromMembershipInNAndNonzero,
    TryVerifyOrderOneLeFromMembershipInNPos,
    TryVerifyOrderOneLeFromMembershipInZAndPositive,
    TryVerifyOrderOppositeSignMulMinusOne,
    TryVerifyPositiveEvenIntegerGreaterThanOne,
    TryVerifyPowEqualsByKnownLogInverse,
    TryVerifyPowerSetFiniteSetSizeEquality,
    TryVerifyProductFromKnownDivisionCandidate,
    TryVerifyProductNonzeroComponentFromKnownProduct,
    TryVerifySetBuilderMembershipDefinitionTransport,
    TryVerifySqrtMonotonicity,
    TryVerifySqrtNotEqualZeroFromPositiveArg,
    TryVerifySqrtOfSquareIdentity,
    TryVerifySqrtProductIdentity,
    TryVerifySqrtQuotientIdentity,
    TryVerifySqrtSquareIdentity,
    TryVerifySqrtZeroOneIdentity,
    TryVerifySquareSumComponentZeroFromKnownSumZero,
    TryVerifySquareSumNotEqualZeroFromNonzeroComponent,
    TryVerifySquareSumZeroFromZeroComponents,
    TryVerifySubNotEqualZeroFromOperandNotEqual,
    TryVerifySymbolicTupleEqualityFromCoordinates,
    TryVerifyTrigonometricEquality,
    TryVerifyTrigonometricIntervalOrder,
    TryVerifyTrigonometricNotEqual,
    TryVerifyTrigonometricOrderBound,
    TryVerifyTupleEqualityFromDimAndProjections,
    TryVerifyTupleReconstructionFromKnownCartMembership,
    TryVerifyZeroEqualsProductImpliesOtherFactorZero,
    TryVerifyZeroPowPositiveExponentIdentity,
    TryVerifyZeroProductOr,
    TryZeroLeMulByWeakSigns,
    TryZeroLtMulBySigns,
    VerifyAdditiveSignWithBuiltinStrategy,
    VerifyAndFactRestrictedKnownBuiltin,
    VerifyBuiltinFunctionPropertyByDefinition,
    VerifyBuiltinProperSetRelationByDefinition,
    VerifyBuiltinProperSetRelationFromQuantifierFreePremise,
    VerifyChoiceFunctionForFactByDefinition,
    VerifyCoprimeFactByDefinition,
    VerifyDvdFactByDefinition,
    VerifyEqualFact,
    VerifyEqualFactByBuiltinRulesAndKnownEqualities,
    VerifyEqualFactByDirectEvaluation,
    VerifyEqualFactByKnownEqualityThenDirectEvaluation,
    VerifyEqualFactWithZeroPremiseVerification,
    VerifyExistFact,
    VerifyExtremumEqualityWithBuiltinStrategy,
    VerifyFiniteNonemptyNaturalSetHasMaximum,
    VerifyFiniteSetProductPointwiseEqualityWithBuiltinStrategy,
    VerifyFnEqualFactWithBuiltinRules,
    VerifyFnEqualInFactWithBuiltinRules,
    VerifyForallFact,
    VerifyForallFactWithIff,
    VerifyGeneralCartNonemptyByChoiceExplicit,
    VerifyInFactAddInNPosFromNPosAndN,
    VerifyInFactAnonymousFnSignatureMatchesFnSet,
    VerifyInFactAnonymousFnSignatureMatchesFnSetThroughEqualSets,
    VerifyInFactArithmeticExpressionInQ,
    VerifyInFactArithmeticExpressionInStandardNegativeSet,
    VerifyInFactArithmeticExpressionInZ,
    VerifyInFactByEqualToOneElementInListSet,
    VerifyInFactByKnownDirectSuperset,
    VerifyInFactByKnownListSetCarrier,
    VerifyInFactByStructObj,
    VerifyInFactElementInFnSetByStoredDefinition,
    VerifyInFactFiniteSeqLiteralApplicationInSet,
    VerifyInFactFnApplicationInFnRange,
    VerifyInFactFnApplicationInTypedReturnSet,
    VerifyInFactFnRangeInPowerSet,
    VerifyInFactInBigUnionByMemberWitness,
    VerifyInFactInGeneralCartByDefiningFacts,
    VerifyInFactInIndexIntersectByPointwiseMembership,
    VerifyInFactInIndexUnionByIndexWitness,
    VerifyInFactInIntersectByMemberOfBothSides,
    VerifyInFactInPowerSetViaSubset,
    VerifyInFactInReplacementByRelationWitness,
    VerifyInFactInSetMinusByMemberAndNonMember,
    VerifyInFactInUnionByMemberOfEitherSide,
    VerifyInFactIntervalByRealOrderBounds,
    VerifyInFactListSetInPowerSetDefinesMembership,
    VerifyInFactLiteralTupleProjectionInSet,
    VerifyInFactMulInNPosFromFactorsInNPos,
    VerifyInFactObjAtIndexInStandardSetByCartFactorListSet,
    VerifyInFactOneSideInfinityIntervalByRealOrderBound,
    VerifyInFactPowInRPosFromPositiveBaseRealExponent,
    VerifyInFactPowInStandardSetFromBaseAndNaturalExponent,
    VerifyInFactSetBuilderInPowerSetViaParamSubset,
    VerifyInFactStructFieldInDefinitionCarrier,
    VerifyInFactSubInNFromIntegerTermsAndBound,
    VerifyInFactSubInNPosFromNPosAndGreaterThanOne,
    VerifyInFactWithBuiltinRules,
    VerifyIndexSetNonemptyPremise,
    VerifyIndexedValueInDefinitionReturnSetViaCartProjection,
    VerifyIsCartFactWithBuiltinRules,
    VerifyIsFiniteSetFactWithBuiltinRules,
    VerifyIsFiniteSetWithBuiltinStrategy,
    VerifyIsNonemptySetFactWithBuiltinRules,
    VerifyIsNonemptySetWithBuiltinStrategy,
    VerifyIsTupleFactWithBuiltinRules,
    VerifyKnownOrConcreteFiniteSetMembership,
    VerifyKnownOrStructurallyFiniteSet,
    VerifyLogOrderBuiltinRule,
    VerifyModCongruenceWithBuiltinStrategy,
    VerifyNegatedOrderFromKnownEquivalentOrder,
    VerifyNonEquationalAtomicFactWithBuiltinRulesInner,
    VerifyNonemptyConstructorStrategy,
    VerifyNonzeroProductWithBuiltinStrategy,
    VerifyNotEqualFactWithBuiltinRules,
    VerifyNotInFactByNotEqualToEveryElementInListSet,
    VerifyNotInFactNotInIntersectByNonMemberOfEitherSide,
    VerifyNotInFactWithBuiltinRules,
    VerifyNotIsNonemptySetFactWithBuiltinRules,
    VerifyNumericCarrierWithBuiltinStrategy,
    VerifyOneLayerSetBuilderMembershipWithBuiltinStrategyOnce,
    VerifyOrFact,
    VerifyOrFactRestrictedKnownBuiltin,
    VerifyOrderAtomicFactNumericBuiltinOnly,
    VerifyOrderFromKnownNegatedComplement,
    VerifyOrderFromKnownZeroOrderOnSubBuiltinRule,
    VerifyPositiveNaturalCarrierStrategy,
    VerifyPrimeFactByDefinition,
    VerifyReduceMembershipFromOperationCarrier,
    VerifyRefinedIntegerCarrierFromKnownSign,
    VerifySetMembershipWithBuiltinStrategy,
    VerifySubsetFactByMembershipForallDefinition,
    VerifySubsetFactWithBuiltinRules,
    VerifySubsetWithBuiltinStrategy,
    VerifySupersetFactByMembershipForallDefinition,
    VerifySupersetFactWithBuiltinRules,
    VerifyValueInDefinitionReturnSet,
    VerifyZeroLeEvenIntegerPowBuiltinRule,
    VerifyZeroLePowFromNonnegativeBasePositiveIntegerExpBuiltinRule,
    VerifyZeroLePowFromPositiveBaseRealExpBuiltinRule,
    VerifyZeroLePowIntegerExponentFromNonnegBaseBuiltinRule,
    VerifyZeroLeSqrtFromNonnegativeArgBuiltinRule,
    VerifyZeroLtEvenIntegerPowFromBaseNonzeroBuiltinRule,
    VerifyZeroLtPowFromPositiveBaseRealExpBuiltinRule,
    VerifyZeroLtSqrtFromPositiveArgBuiltinRule,
}

impl UncataloguedBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::ComplexEqualityResultWithSteps => "builtin.verify.verify_builtin_rules.complex_builtin.complex_equality_result_with_steps",
            Self::ComplexOrderResult => "builtin.verify.verify_builtin_rules.complex_builtin.complex_order_result",
            Self::DecompositionParts => "builtin.verify.verify_builtin_rules.equality_numeric.elementary.decomposition_parts",
            Self::ExecBuiltinThmStmtImpl => "builtin.execute.explicit_verify.theorem_application.exec_builtin_thm_stmt_impl",
            Self::ExecuteTrustedFact => "builtin.execute.submitted_fact_execution.execute_trusted_fact",
            Self::FactualEqualSuccessByBuiltinReasonWithSubgoals => "builtin.verify.equality.patterns.factual_equal_success_by_builtin_reason_with_subgoals",
            Self::FnSetEqualityVerifiedByBuiltinRulesResult => "builtin.verify.equality.function_set.fn_set_equality_verified_by_builtin_rules_result",
            Self::IndexedFamilySubsetSuccess => "builtin.verify.verify_builtin_rules.indexed_set_family.indexed_family_subset_success",
            Self::MaybeVerifyInFactFiniteSetExtremum => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.maybe_verify_in_fact_finite_set_extremum",
            Self::MaybeVerifyInFactInUnfoldedUserDefinedSetOnce => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.maybe_verify_in_fact_in_unfolded_user_defined_set_once",
            Self::NativeEqualSuccess => "builtin.verify.verify_builtin_rules.native_exp_sign_factorial.native_equal_success",
            Self::NotInFactVerifiedByBuiltinRulesResult => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_values.not_in_fact_verified_by_builtin_rules_result",
            Self::NumberInSetVerifiedByBuiltinRulesResult => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_values.number_in_set_verified_by_builtin_rules_result",
            Self::NumberInSetVerifiedByBuiltinRulesResultWithSubgoals => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_values.number_in_set_verified_by_builtin_rules_result_with_subgoals",
            Self::PythagoreanCoreResult => "builtin.verify.verify_builtin_rules.trigonometry.pythagorean_core_result",
            Self::SetEqualitySuccess => "builtin.verify.verify_builtin_rules.equality_dispatch.set_equality_success",
            Self::TestFixture => "builtin.test.fixture",
            Self::TrigCoreDependencyResults => "builtin.verify.verify_builtin_rules.trigonometry.trig_core_dependency_results",
            Self::TryAbsLeFromEvenPowerLe => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_abs_le_from_even_power_le",
            Self::TryBaseLeFromPowLeSamePositiveIntegerExponentNonnegativeBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_base_le_from_pow_le_same_positive_integer_exponent_nonnegative_base",
            Self::TryBaseLeFromPowLeSamePositiveRealExponentPositiveBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_base_le_from_pow_le_same_positive_real_exponent_positive_base",
            Self::TryBaseLtFromPowLtSamePositiveRealExponentPositiveBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_base_lt_from_pow_lt_same_positive_real_exponent_positive_base",
            Self::TryLessAlgebra => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_less_algebra",
            Self::TryLessEqualAlgebra => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_less_equal_algebra",
            Self::TryLessEqualFiniteSetSumPointwiseOnSameSet => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_less_equal_finite_set_sum_pointwise_on_same_set",
            Self::TryLessEqualFiniteSetSummandNonnegativeSum => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_less_equal_finite_set_summand_nonnegative_sum",
            Self::TryLessEqualFromPositiveDenominatorBound => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_less_equal_from_positive_denominator_bound",
            Self::TryLessEqualFromPositiveDivisionProductBound => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_less_equal_from_positive_division_product_bound",
            Self::TryMulLeComponentwiseNonnegativeFactors => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_mul_le_componentwise_nonnegative_factors",
            Self::TryMulLeSharedLeft => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_mul_le_shared_left",
            Self::TryMulLeZeroByWeakSigns => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_mul_le_zero_by_weak_signs",
            Self::TryMulLtSharedLeft => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_mul_lt_shared_left",
            Self::TryMulLtZeroBySigns => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_mul_lt_zero_by_signs",
            Self::TryPowLeEvenExponentFromAbsLe => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_le_even_exponent_from_abs_le",
            Self::TryPowLeSameNegativeIntegerExponentPositiveBaseReversesOrder => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_le_same_negative_integer_exponent_positive_base_reverses_order",
            Self::TryPowLeSamePositiveIntegerExponentNonnegativeBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_le_same_positive_integer_exponent_nonnegative_base",
            Self::TryPowLeSamePositiveOddIntegerExponent => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_le_same_positive_odd_integer_exponent",
            Self::TryPowLeZeroOddExponentFromNonpositiveBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_le_zero_odd_exponent_from_nonpositive_base",
            Self::TryPowLtEvenExponentFromAbsLt => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_lt_even_exponent_from_abs_lt",
            Self::TryPowLtSamePositiveIntegerExponentNonnegativeBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_lt_same_positive_integer_exponent_nonnegative_base",
            Self::TryPowLtSamePositiveOddIntegerExponent => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_lt_same_positive_odd_integer_exponent",
            Self::TryPowLtSamePositiveRealExponentPositiveBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_lt_same_positive_real_exponent_positive_base",
            Self::TryPowLtZeroOddExponentFromNegativeBase => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_pow_lt_zero_odd_exponent_from_negative_base",
            Self::TryTrigQuotientDefinition => "builtin.verify.verify_builtin_rules.trigonometry.try_trig_quotient_definition",
            Self::TryVerifyAbsFiniteSetSumTriangle => "builtin.verify.verify_builtin_rules.abs_order_builtin.try_verify_abs_finite_set_sum_triangle",
            Self::TryVerifyAbsFiniteSumTriangle => "builtin.verify.verify_builtin_rules.abs_order_builtin.try_verify_abs_finite_sum_triangle",
            Self::TryVerifyAbsLowerBoundFromAbsCompare => "builtin.verify.verify_builtin_rules.abs_order_builtin.try_verify_abs_lower_bound_from_abs_compare",
            Self::TryVerifyAbsNotEqualZeroFromArgNonzero => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_abs_not_equal_zero_from_arg_nonzero",
            Self::TryVerifyAbsUpperBound => "builtin.verify.verify_builtin_rules.abs_order_builtin.try_verify_abs_upper_bound",
            Self::TryVerifyAddNotEqualZeroFromOperandNotEqualNegation => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_add_not_equal_zero_from_operand_not_equal_negation",
            Self::TryVerifyArcsinInverseEquality => "builtin.verify.verify_builtin_rules.trigonometry.try_verify_arcsin_inverse_equality",
            Self::TryVerifyArcsinPrincipalRange => "builtin.verify.verify_builtin_rules.trigonometry.try_verify_arcsin_principal_range",
            Self::TryVerifyAtomicFactFromKnownSetBuilderMembership => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.try_verify_atomic_fact_from_known_set_builder_membership",
            Self::TryVerifyCartEqualityFromDimAndProjections => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_cart_equality_from_dim_and_projections",
            Self::TryVerifyComponentNonzeroOrFromKnownSquareSumNotEqualZero => "builtin.verify.composite.disjunction.try_verify_component_nonzero_or_from_known_square_sum_not_equal_zero",
            Self::TryVerifyDivNotEqualZeroFromNumeratorNonzero => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_div_not_equal_zero_from_numerator_nonzero",
            Self::TryVerifyDivisionFromKnownProduct => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_division_from_known_product",
            Self::TryVerifyEmptyFiniteSetFromSizeZero => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_empty_finite_set_from_size_zero",
            Self::TryVerifyEmptySetEqualityFromNotNonempty => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_empty_set_equality_from_not_nonempty",
            Self::TryVerifyEqualityFromTwoSidedWeakOrder => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_equality_from_two_sided_weak_order",
            Self::TryVerifyFiniteCodomainFromKnownSurjection => "builtin.verify.verify_builtin_rules.mapping_properties_builtin.try_verify_finite_codomain_from_known_surjection",
            Self::TryVerifyFiniteNonemptySetSizeAtLeastOne => "builtin.verify.verify_builtin_rules.number_compare.try_verify_finite_nonempty_set_size_at_least_one",
            Self::TryVerifyFiniteSetExtremaOrderBuiltinRule => "builtin.verify.verify_builtin_rules.order_semantics_builtin.try_verify_finite_set_extrema_order_builtin_rule",
            Self::TryVerifyFiniteSetProductPointwiseEquality => "builtin.verify.verify_builtin_rules.equality_numeric.finite_set_product.try_verify_finite_set_product_pointwise_equality",
            Self::TryVerifyFiniteSetSizeCodomainLeDomainFromKnownSurjection => "builtin.verify.verify_builtin_rules.mapping_properties_builtin.try_verify_finite_set_size_codomain_le_domain_from_known_surjection",
            Self::TryVerifyFiniteSetSizeFnRangeFromKnownInjection => "builtin.verify.verify_builtin_rules.mapping_properties_builtin.try_verify_finite_set_size_fn_range_from_known_injection",
            Self::TryVerifyFiniteSetSizeFromKnownBijection => "builtin.verify.verify_builtin_rules.mapping_properties_builtin.try_verify_finite_set_size_from_known_bijection",
            Self::TryVerifyFiniteSetSizeIntegerRangeEquality => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_finite_set_size_integer_range_equality",
            Self::TryVerifyFiniteSetSizeNonnegative => "builtin.verify.verify_builtin_rules.number_compare.try_verify_finite_set_size_nonnegative",
            Self::TryVerifyFiniteSetSizePartitionEquality => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_finite_set_size_partition_equality",
            Self::TryVerifyFiniteSetSizeSetMinusEquality => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_finite_set_size_set_minus_equality",
            Self::TryVerifyFiniteSetSizeSetMinusOfSubsetEquality => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_finite_set_size_set_minus_of_subset_equality",
            Self::TryVerifyFiniteSetSizeSubsetLe => "builtin.verify.verify_builtin_rules.number_compare.try_verify_finite_set_size_subset_le",
            Self::TryVerifyFiniteSetSizeUnionEquality => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_finite_set_size_union_equality",
            Self::TryVerifyFiniteSetSizeUnionLeSum => "builtin.verify.verify_builtin_rules.number_compare.try_verify_finite_set_size_union_le_sum",
            Self::TryVerifyFiniteSetSumSubstitution => "builtin.verify.verify_builtin_rules.equality_numeric.finite_set_sum.try_verify_finite_set_sum_substitution",
            Self::TryVerifyInFactBySymbolicCart => "builtin.verify.verify_builtin_rules.in_fact_builtin.cart_membership.try_verify_in_fact_by_symbolic_cart",
            Self::TryVerifyIndexedSetFamilyEqualities => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_indexed_set_family_equalities",
            Self::TryVerifyIntegerDiscreteSplitOrBuiltinRule => "builtin.verify.verify_builtin_rules.order_semantics_builtin.try_verify_integer_discrete_split_or_builtin_rule",
            Self::TryVerifyIntegerSingletonIntervalEqualityBuiltinRule => "builtin.verify.verify_builtin_rules.order_semantics_builtin.try_verify_integer_singleton_interval_equality_builtin_rule",
            Self::TryVerifyIntegerSuccessorPredecessorBuiltinRule => "builtin.verify.verify_builtin_rules.order_semantics_builtin.try_verify_integer_successor_predecessor_builtin_rule",
            Self::TryVerifyIntegerSuccessorTailOrFromLowerBound => "builtin.verify.composite.disjunction.try_verify_integer_successor_tail_or_from_lower_bound",
            Self::TryVerifyIntrinsicallyPositiveNativeValueNonzero => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_intrinsically_positive_native_value_nonzero",
            Self::TryVerifyLiteralSetIntersectionFilter => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_literal_set_intersection_filter",
            Self::TryVerifyMinusOneOddNaturalPower => "builtin.verify.verify_builtin_rules.equality_numeric.power_identities.try_verify_minus_one_odd_natural_power",
            Self::TryVerifyModDividendMinusRemainderEqualsZero => "builtin.verify.verify_builtin_rules.equality_numeric.elementary.try_verify_mod_dividend_minus_remainder_equals_zero",
            Self::TryVerifyModEqRemainderFromEuclideanDivision => "builtin.verify.verify_builtin_rules.equality_numeric.elementary.try_verify_mod_eq_remainder_from_euclidean_division",
            Self::TryVerifyModRemainderBounds => "builtin.verify.verify_builtin_rules.number_compare.try_verify_mod_remainder_bounds",
            Self::TryVerifyNativeComplexAbsNonzero => "builtin.verify.verify_builtin_rules.complex_builtin.try_verify_native_complex_abs_nonzero",
            Self::TryVerifyNativeExpLnMonotonicity => "builtin.verify.verify_builtin_rules.native_exp_sign_factorial.try_verify_native_exp_ln_monotonicity",
            Self::TryVerifyNativeExpSignFactorialOrder => "builtin.verify.verify_builtin_rules.native_exp_sign_factorial.try_verify_native_exp_sign_factorial_order",
            Self::TryVerifyNativeFactorialMonotonicity => "builtin.verify.verify_builtin_rules.native_exp_sign_factorial.try_verify_native_factorial_monotonicity",
            Self::TryVerifyNativeINonzero => "builtin.verify.verify_builtin_rules.complex_builtin.try_verify_native_i_nonzero",
            Self::TryVerifyNativeLcmBasicEquality => "builtin.verify.verify_builtin_rules.native_integer_extrema.try_verify_native_lcm_basic_equality",
            Self::TryVerifyNativeLcmGcdProductEquality => "builtin.verify.verify_builtin_rules.native_integer_extrema.try_verify_native_lcm_gcd_product_equality",
            Self::TryVerifyNativeLcmLeCommonPositiveMultiple => "builtin.verify.verify_builtin_rules.native_integer_extrema.try_verify_native_lcm_le_common_positive_multiple",
            Self::TryVerifyNativeRealConstantNonzero => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_native_real_constant_nonzero",
            Self::TryVerifyNativeRealConstantPositive => "builtin.verify.verify_builtin_rules.number_compare.try_verify_native_real_constant_positive",
            Self::TryVerifyNativeRoundingAlgebraEquality => "builtin.verify.verify_builtin_rules.native_integer_extrema.try_verify_native_rounding_algebra_equality",
            Self::TryVerifyNativeRoundingExtremaMonotonicity => "builtin.verify.verify_builtin_rules.native_integer_extrema.try_verify_native_rounding_extrema_monotonicity",
            Self::TryVerifyNativeRoundingExtremaOrder => "builtin.verify.verify_builtin_rules.native_integer_extrema.try_verify_native_rounding_extrema_order",
            Self::TryVerifyNativeRoundingIntegerEquality => "builtin.verify.verify_builtin_rules.native_integer_extrema.try_verify_native_rounding_integer_equality",
            Self::TryVerifyNativeSignMonotonicity => "builtin.verify.verify_builtin_rules.native_exp_sign_factorial.try_verify_native_sign_monotonicity",
            Self::TryVerifyNativeSignNonzeroCharacterization => "builtin.verify.verify_builtin_rules.native_exp_sign_factorial.try_verify_native_sign_nonzero_characterization",
            Self::TryVerifyNonemptyFiniteSetFromPositiveFiniteSetSize => "builtin.verify.verify_builtin_rules.type_predicates_builtin.try_verify_nonempty_finite_set_from_positive_finite_set_size",
            Self::TryVerifyNotEqualEmptySetFromNonempty => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_not_equal_empty_set_from_nonempty",
            Self::TryVerifyNotEqualFactWhenZeroAndBinaryArithmeticReducesByOperandFacts => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts",
            Self::TryVerifyNotEqualFromKnownPositiveLowerBound => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_not_equal_from_known_positive_lower_bound",
            Self::TryVerifyNotEqualFromKnownStrictOrder => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_not_equal_from_known_strict_order",
            Self::TryVerifyNotEqualFromMembershipContradiction => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_not_equal_from_membership_contradiction",
            Self::TryVerifyNotEqualPowFromBaseNonzero => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_not_equal_pow_from_base_nonzero",
            Self::TryVerifyNotEqualZeroFromNAndOneLe => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_not_equal_zero_from_n_and_one_le",
            Self::TryVerifyNumericLowerBoundFromKnownLowerBound => "builtin.verify.verify_builtin_rules.number_compare.try_verify_numeric_lower_bound_from_known_lower_bound",
            Self::TryVerifyNumericUpperBoundFromKnownUpperBound => "builtin.verify.verify_builtin_rules.number_compare.try_verify_numeric_upper_bound_from_known_upper_bound",
            Self::TryVerifyOneModEqualsOneForModulusAtLeastTwo => "builtin.verify.verify_builtin_rules.equality_numeric.elementary.try_verify_one_mod_equals_one_for_modulus_at_least_two",
            Self::TryVerifyOneSubtractionFromKnownAddition => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_one_subtraction_from_known_addition",
            Self::TryVerifyOperandNotEqualFromSubNotEqualZero => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_operand_not_equal_from_sub_not_equal_zero",
            Self::TryVerifyOperandNotEqualNegationFromAddNotEqualZero => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_operand_not_equal_negation_from_add_not_equal_zero",
            Self::TryVerifyOrByClassicalImplication => "builtin.verify.composite.disjunction.try_verify_or_by_classical_implication",
            Self::TryVerifyOrderNonnegativeFromMembershipInN => "builtin.verify.verify_builtin_rules.number_compare.try_verify_order_nonnegative_from_membership_in_n",
            Self::TryVerifyOrderOneLeFromMembershipInNAndNonzero => "builtin.verify.verify_builtin_rules.number_compare.try_verify_order_one_le_from_membership_in_n_and_nonzero",
            Self::TryVerifyOrderOneLeFromMembershipInNPos => "builtin.verify.verify_builtin_rules.number_compare.try_verify_order_one_le_from_membership_in_n_pos",
            Self::TryVerifyOrderOneLeFromMembershipInZAndPositive => "builtin.verify.verify_builtin_rules.number_compare.try_verify_order_one_le_from_membership_in_z_and_positive",
            Self::TryVerifyOrderOppositeSignMulMinusOne => "builtin.verify.verify_builtin_rules.number_compare.try_verify_order_opposite_sign_mul_minus_one",
            Self::TryVerifyPositiveEvenIntegerGreaterThanOne => "builtin.verify.verify_builtin_rules.order_semantics_builtin.try_verify_positive_even_integer_greater_than_one",
            Self::TryVerifyPowEqualsByKnownLogInverse => "builtin.verify.verify_builtin_rules.equality_numeric.logarithms.try_verify_pow_equals_by_known_log_inverse",
            Self::TryVerifyPowerSetFiniteSetSizeEquality => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_power_set_finite_set_size_equality",
            Self::TryVerifyProductFromKnownDivisionCandidate => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_product_from_known_division_candidate",
            Self::TryVerifyProductNonzeroComponentFromKnownProduct => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_product_nonzero_component_from_known_product",
            Self::TryVerifySetBuilderMembershipDefinitionTransport => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.try_verify_set_builder_membership_definition_transport",
            Self::TryVerifySqrtMonotonicity => "builtin.verify.verify_builtin_rules.number_compare.try_verify_sqrt_monotonicity",
            Self::TryVerifySqrtNotEqualZeroFromPositiveArg => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_sqrt_not_equal_zero_from_positive_arg",
            Self::TryVerifySqrtOfSquareIdentity => "builtin.verify.verify_builtin_rules.equality_numeric.square_root.try_verify_sqrt_of_square_identity",
            Self::TryVerifySqrtProductIdentity => "builtin.verify.verify_builtin_rules.equality_numeric.square_root.try_verify_sqrt_product_identity",
            Self::TryVerifySqrtQuotientIdentity => "builtin.verify.verify_builtin_rules.equality_numeric.square_root.try_verify_sqrt_quotient_identity",
            Self::TryVerifySqrtSquareIdentity => "builtin.verify.verify_builtin_rules.equality_numeric.square_root.try_verify_sqrt_square_identity",
            Self::TryVerifySqrtZeroOneIdentity => "builtin.verify.verify_builtin_rules.equality_numeric.square_root.try_verify_sqrt_zero_one_identity",
            Self::TryVerifySquareSumComponentZeroFromKnownSumZero => "builtin.verify.verify_builtin_rules.equality_numeric.square_sums.try_verify_square_sum_component_zero_from_known_sum_zero",
            Self::TryVerifySquareSumNotEqualZeroFromNonzeroComponent => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_square_sum_not_equal_zero_from_nonzero_component",
            Self::TryVerifySquareSumZeroFromZeroComponents => "builtin.verify.verify_builtin_rules.equality_numeric.square_sums.try_verify_square_sum_zero_from_zero_components",
            Self::TryVerifySubNotEqualZeroFromOperandNotEqual => "builtin.verify.verify_builtin_rules.not_equal_builtin.try_verify_sub_not_equal_zero_from_operand_not_equal",
            Self::TryVerifySymbolicTupleEqualityFromCoordinates => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_symbolic_tuple_equality_from_coordinates",
            Self::TryVerifyTrigonometricEquality => "builtin.verify.verify_builtin_rules.trigonometry.try_verify_trigonometric_equality",
            Self::TryVerifyTrigonometricIntervalOrder => "builtin.verify.verify_builtin_rules.trigonometry.try_verify_trigonometric_interval_order",
            Self::TryVerifyTrigonometricNotEqual => "builtin.verify.verify_builtin_rules.trigonometry.try_verify_trigonometric_not_equal",
            Self::TryVerifyTrigonometricOrderBound => "builtin.verify.verify_builtin_rules.trigonometry.try_verify_trigonometric_order_bound",
            Self::TryVerifyTupleEqualityFromDimAndProjections => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_tuple_equality_from_dim_and_projections",
            Self::TryVerifyTupleReconstructionFromKnownCartMembership => "builtin.verify.verify_builtin_rules.equality_dispatch.try_verify_tuple_reconstruction_from_known_cart_membership",
            Self::TryVerifyZeroEqualsProductImpliesOtherFactorZero => "builtin.verify.verify_builtin_rules.equality_numeric.elementary.try_verify_zero_equals_product_implies_other_factor_zero",
            Self::TryVerifyZeroPowPositiveExponentIdentity => "builtin.verify.verify_builtin_rules.equality_numeric.power_identities.try_verify_zero_pow_positive_exponent_identity",
            Self::TryVerifyZeroProductOr => "builtin.verify.composite.disjunction.try_verify_zero_product_or",
            Self::TryZeroLeMulByWeakSigns => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_zero_le_mul_by_weak_signs",
            Self::TryZeroLtMulBySigns => "builtin.verify.verify_builtin_rules.order_algebra_builtin.try_zero_lt_mul_by_signs",
            Self::VerifyAdditiveSignWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.numeric_sign.verify_additive_sign_with_builtin_strategy",
            Self::VerifyAndFactRestrictedKnownBuiltin => "builtin.verify.support.helper.verify_and_fact_restricted_known_builtin",
            Self::VerifyBuiltinFunctionPropertyByDefinition => "builtin.verify.atomic.function_properties.verify_builtin_function_property_by_definition",
            Self::VerifyBuiltinProperSetRelationByDefinition => "builtin.verify.atomic.set_relations.verify_builtin_proper_set_relation_by_definition",
            Self::VerifyBuiltinProperSetRelationFromQuantifierFreePremise => "builtin.verify.atomic.set_relations.verify_builtin_proper_set_relation_from_quantifier_free_premise",
            Self::VerifyChoiceFunctionForFactByDefinition => "builtin.verify.atomic.definition.verify_choice_function_for_fact_by_definition",
            Self::VerifyCoprimeFactByDefinition => "builtin.verify.atomic.definition.verify_coprime_fact_by_definition",
            Self::VerifyDvdFactByDefinition => "builtin.verify.atomic.definition.verify_dvd_fact_by_definition",
            Self::VerifyEqualFact => "builtin.verify.equality.core.verify_equal_fact",
            Self::VerifyEqualFactByBuiltinRulesAndKnownEqualities => "builtin.verify.equality.core.verify_equal_fact_by_builtin_rules_and_known_equalities",
            Self::VerifyEqualFactByDirectEvaluation => "builtin.verify.equality.core.verify_equal_fact_by_direct_evaluation",
            Self::VerifyEqualFactByKnownEqualityThenDirectEvaluation => "builtin.verify.equality.core.verify_equal_fact_by_known_equality_then_direct_evaluation",
            Self::VerifyEqualFactWithZeroPremiseVerification => "builtin.verify.equality.core.verify_equal_fact_with_zero_premise_verification",
            Self::VerifyExistFact => "builtin.verify.quantified.existential.verify_exist_fact",
            Self::VerifyExtremumEqualityWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.equality.verify_extremum_equality_with_builtin_strategy",
            Self::VerifyFiniteNonemptyNaturalSetHasMaximum => "builtin.verify.quantified.existential.verify_finite_nonempty_natural_set_has_maximum",
            Self::VerifyFiniteSetProductPointwiseEqualityWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.equality.verify_finite_set_product_pointwise_equality_with_builtin_strategy",
            Self::VerifyFnEqualFactWithBuiltinRules => "builtin.verify.equality.function.verify_fn_equal_fact_with_builtin_rules",
            Self::VerifyFnEqualInFactWithBuiltinRules => "builtin.verify.equality.function.verify_fn_equal_in_fact_with_builtin_rules",
            Self::VerifyForallFact => "builtin.verify.quantified.universal.verify_forall_fact",
            Self::VerifyForallFactWithIff => "builtin.verify.quantified.universal_iff.verify_forall_fact_with_iff",
            Self::VerifyGeneralCartNonemptyByChoiceExplicit => "builtin.verify.verify_builtin_rules.type_predicates_builtin.verify_general_cart_nonempty_by_choice_explicit",
            Self::VerifyInFactAddInNPosFromNPosAndN => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_add_in_n_pos_from_n_pos_and_n",
            Self::VerifyInFactAnonymousFnSignatureMatchesFnSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_anonymous_fn_signature_matches_fn_set",
            Self::VerifyInFactAnonymousFnSignatureMatchesFnSetThroughEqualSets => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_anonymous_fn_signature_matches_fn_set_through_equal_sets",
            Self::VerifyInFactArithmeticExpressionInQ => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_arithmetic_expression_in_q",
            Self::VerifyInFactArithmeticExpressionInStandardNegativeSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_arithmetic_expression_in_standard_negative_set",
            Self::VerifyInFactArithmeticExpressionInZ => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_arithmetic_expression_in_z",
            Self::VerifyInFactByEqualToOneElementInListSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_by_equal_to_one_element_in_list_set",
            Self::VerifyInFactByKnownDirectSuperset => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_by_known_direct_superset",
            Self::VerifyInFactByKnownListSetCarrier => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_by_known_list_set_carrier",
            Self::VerifyInFactByStructObj => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_by_struct_obj",
            Self::VerifyInFactElementInFnSetByStoredDefinition => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_element_in_fn_set_by_stored_definition",
            Self::VerifyInFactFiniteSeqLiteralApplicationInSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_finite_seq_literal_application_in_set",
            Self::VerifyInFactFnApplicationInFnRange => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_fn_application_in_fn_range",
            Self::VerifyInFactFnApplicationInTypedReturnSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_fn_application_in_typed_return_set",
            Self::VerifyInFactFnRangeInPowerSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_fn_range_in_power_set",
            Self::VerifyInFactInBigUnionByMemberWitness => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_big_union_by_member_witness",
            Self::VerifyInFactInGeneralCartByDefiningFacts => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_general_cart_by_defining_facts",
            Self::VerifyInFactInIndexIntersectByPointwiseMembership => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_index_intersect_by_pointwise_membership",
            Self::VerifyInFactInIndexUnionByIndexWitness => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_index_union_by_index_witness",
            Self::VerifyInFactInIntersectByMemberOfBothSides => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_intersect_by_member_of_both_sides",
            Self::VerifyInFactInPowerSetViaSubset => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_power_set_via_subset",
            Self::VerifyInFactInReplacementByRelationWitness => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_replacement_by_relation_witness",
            Self::VerifyInFactInSetMinusByMemberAndNonMember => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_set_minus_by_member_and_non_member",
            Self::VerifyInFactInUnionByMemberOfEitherSide => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_in_fact_in_union_by_member_of_either_side",
            Self::VerifyInFactIntervalByRealOrderBounds => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_interval_by_real_order_bounds",
            Self::VerifyInFactListSetInPowerSetDefinesMembership => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_list_set_in_power_set_defines_membership",
            Self::VerifyInFactLiteralTupleProjectionInSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_literal_tuple_projection_in_set",
            Self::VerifyInFactMulInNPosFromFactorsInNPos => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_mul_in_n_pos_from_factors_in_n_pos",
            Self::VerifyInFactObjAtIndexInStandardSetByCartFactorListSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_obj_at_index_in_standard_set_by_cart_factor_list_set",
            Self::VerifyInFactOneSideInfinityIntervalByRealOrderBound => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_one_side_infinity_interval_by_real_order_bound",
            Self::VerifyInFactPowInRPosFromPositiveBaseRealExponent => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_pow_in_r_pos_from_positive_base_real_exponent",
            Self::VerifyInFactPowInStandardSetFromBaseAndNaturalExponent => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_pow_in_standard_set_from_base_and_natural_exponent",
            Self::VerifyInFactSetBuilderInPowerSetViaParamSubset => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_set_builder_in_power_set_via_param_subset",
            Self::VerifyInFactStructFieldInDefinitionCarrier => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_in_fact_struct_field_in_definition_carrier",
            Self::VerifyInFactSubInNFromIntegerTermsAndBound => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_sub_in_n_from_integer_terms_and_bound",
            Self::VerifyInFactSubInNPosFromNPosAndGreaterThanOne => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_in_fact_sub_in_n_pos_from_n_pos_and_greater_than_one",
            Self::VerifyInFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.in_fact_builtin.dispatch.verify_in_fact_with_builtin_rules",
            Self::VerifyIndexSetNonemptyPremise => "builtin.verify.verify_builtin_rules.indexed_set_family.verify_index_set_nonempty_premise",
            Self::VerifyIndexedValueInDefinitionReturnSetViaCartProjection => "builtin.verify.atomic.function_membership.verify_indexed_value_in_definition_return_set_via_cart_projection",
            Self::VerifyIsCartFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.type_predicates_builtin._verify_is_cart_fact_with_builtin_rules",
            Self::VerifyIsFiniteSetFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.type_predicates_builtin._verify_is_finite_set_fact_with_builtin_rules",
            Self::VerifyIsFiniteSetWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.type_predicates.verify_is_finite_set_with_builtin_strategy",
            Self::VerifyIsNonemptySetFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.type_predicates_builtin._verify_is_nonempty_set_fact_with_builtin_rules",
            Self::VerifyIsNonemptySetWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.type_predicates.verify_is_nonempty_set_with_builtin_strategy",
            Self::VerifyIsTupleFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.type_predicates_builtin._verify_is_tuple_fact_with_builtin_rules",
            Self::VerifyKnownOrConcreteFiniteSetMembership => "builtin.verify.verify_builtin_rules.order_semantics_builtin.verify_known_or_concrete_finite_set_membership",
            Self::VerifyKnownOrStructurallyFiniteSet => "builtin.verify.verify_builtin_rules.mapping_properties_builtin.verify_known_or_structurally_finite_set",
            Self::VerifyLogOrderBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_log_order_builtin_rule",
            Self::VerifyModCongruenceWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.equality.verify_mod_congruence_with_builtin_strategy",
            Self::VerifyNegatedOrderFromKnownEquivalentOrder => "builtin.verify.verify_builtin_rules.number_compare.verify_negated_order_from_known_equivalent_order",
            Self::VerifyNonEquationalAtomicFactWithBuiltinRulesInner => "builtin.verify.verify_builtin_rules.non_equational_dispatch.verify_non_equational_atomic_fact_with_builtin_rules_inner",
            Self::VerifyNonemptyConstructorStrategy => "builtin.verify.verify_builtin_strategies.type_predicates.verify_nonempty_constructor_strategy",
            Self::VerifyNonzeroProductWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.nonzero.verify_nonzero_product_with_builtin_strategy",
            Self::VerifyNotEqualFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.not_equal_builtin._verify_not_equal_fact_with_builtin_rules",
            Self::VerifyNotInFactByNotEqualToEveryElementInListSet => "builtin.verify.verify_builtin_rules.in_fact_builtin.structured_membership.verify_not_in_fact_by_not_equal_to_every_element_in_list_set",
            Self::VerifyNotInFactNotInIntersectByNonMemberOfEitherSide => "builtin.verify.verify_builtin_rules.in_fact_builtin.set_membership.verify_not_in_fact_not_in_intersect_by_non_member_of_either_side",
            Self::VerifyNotInFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.in_fact_builtin.dispatch.verify_not_in_fact_with_builtin_rules",
            Self::VerifyNotIsNonemptySetFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.type_predicates_builtin._verify_not_is_nonempty_set_fact_with_builtin_rules",
            Self::VerifyNumericCarrierWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.numeric_carrier.verify_numeric_carrier_with_builtin_strategy",
            Self::VerifyOneLayerSetBuilderMembershipWithBuiltinStrategyOnce => "builtin.verify.verify_builtin_strategies.set_membership.verify_one_layer_set_builder_membership_with_builtin_strategy_once",
            Self::VerifyOrFact => "builtin.verify.composite.disjunction.verify_or_fact",
            Self::VerifyOrFactRestrictedKnownBuiltin => "builtin.verify.support.helper.verify_or_fact_restricted_known_builtin",
            Self::VerifyOrderAtomicFactNumericBuiltinOnly => "builtin.verify.verify_builtin_rules.number_compare.verify_order_atomic_fact_numeric_builtin_only",
            Self::VerifyOrderFromKnownNegatedComplement => "builtin.verify.verify_builtin_rules.number_compare.verify_order_from_known_negated_complement",
            Self::VerifyOrderFromKnownZeroOrderOnSubBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_order_from_known_zero_order_on_sub_builtin_rule",
            Self::VerifyPositiveNaturalCarrierStrategy => "builtin.verify.verify_builtin_strategies.numeric_carrier.verify_positive_natural_carrier_strategy",
            Self::VerifyPrimeFactByDefinition => "builtin.verify.atomic.definition.verify_prime_fact_by_definition",
            Self::VerifyReduceMembershipFromOperationCarrier => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_reduce_membership_from_operation_carrier",
            Self::VerifyRefinedIntegerCarrierFromKnownSign => "builtin.verify.verify_builtin_rules.in_fact_builtin.numeric_membership.verify_refined_integer_carrier_from_known_sign",
            Self::VerifySetMembershipWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.set_membership.verify_set_membership_with_builtin_strategy",
            Self::VerifySubsetFactByMembershipForallDefinition => "builtin.verify.atomic.definition.verify_subset_fact_by_membership_forall_definition",
            Self::VerifySubsetFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.set_relation_duality.verify_subset_fact_with_builtin_rules",
            Self::VerifySubsetWithBuiltinStrategy => "builtin.verify.verify_builtin_strategies.set_membership.verify_subset_with_builtin_strategy",
            Self::VerifySupersetFactByMembershipForallDefinition => "builtin.verify.atomic.definition.verify_superset_fact_by_membership_forall_definition",
            Self::VerifySupersetFactWithBuiltinRules => "builtin.verify.verify_builtin_rules.set_relation_duality.verify_superset_fact_with_builtin_rules",
            Self::VerifyValueInDefinitionReturnSet => "builtin.verify.atomic.function_membership.verify_value_in_definition_return_set",
            Self::VerifyZeroLeEvenIntegerPowBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_le_even_integer_pow_builtin_rule",
            Self::VerifyZeroLePowFromNonnegativeBasePositiveIntegerExpBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_le_pow_from_nonnegative_base_positive_integer_exp_builtin_rule",
            Self::VerifyZeroLePowFromPositiveBaseRealExpBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_le_pow_from_positive_base_real_exp_builtin_rule",
            Self::VerifyZeroLePowIntegerExponentFromNonnegBaseBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_le_pow_integer_exponent_from_nonneg_base_builtin_rule",
            Self::VerifyZeroLeSqrtFromNonnegativeArgBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_le_sqrt_from_nonnegative_arg_builtin_rule",
            Self::VerifyZeroLtEvenIntegerPowFromBaseNonzeroBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_lt_even_integer_pow_from_base_nonzero_builtin_rule",
            Self::VerifyZeroLtPowFromPositiveBaseRealExpBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_lt_pow_from_positive_base_real_exp_builtin_rule",
            Self::VerifyZeroLtSqrtFromPositiveArgBuiltinRule => "builtin.verify.verify_builtin_rules.number_compare.verify_zero_lt_sqrt_from_positive_arg_builtin_rule",
        }
    }
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonzeroExpressionOrientation {
    ExpressionOnLeft,
    ExpressionOnRight,
}

#[derive(Clone)]
pub struct DivNotEqualZeroBuiltinRuleEvidence {
    pub numerator: Obj,
    pub denominator: Obj,
    pub orientation: NonzeroExpressionOrientation,
}

/// Exact introduction certificate for one selected branch of an `or` fact.
/// The enclosing result retains exactly one child proving
/// `expected_selected`; `selected_index` fixes its position in
/// `expected_target`.
#[derive(Clone)]
pub struct DisjunctionIntroductionBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_selected: Fact,
    pub selected_index: usize,
}

impl DisjunctionIntroductionBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_selected: Fact, selected_index: usize) -> Self {
        Self {
            expected_target,
            expected_selected,
            selected_index,
        }
    }
}

impl fmt::Debug for DisjunctionIntroductionBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("DisjunctionIntroductionBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("expected_selected", &self.expected_selected.to_string())
            .field("selected_index", &self.selected_index)
            .finish()
    }
}

/// A checked equality with one exact source position introduces membership in
/// a finite list-set literal. The enclosing result retains that equality as
/// its sole child; the index fixes the coproduct injection path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListSetMembershipBuiltinRuleEvidence {
    pub selected_index: usize,
}

impl DivNotEqualZeroBuiltinRuleEvidence {
    pub fn rule_id(&self) -> &'static str {
        "nonzero.div"
    }

    pub fn new(
        numerator: Obj,
        denominator: Obj,
        orientation: NonzeroExpressionOrientation,
    ) -> Self {
        Self {
            numerator,
            denominator,
            orientation,
        }
    }
}

impl fmt::Debug for DivNotEqualZeroBuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("DivNotEqualZeroBuiltinRuleEvidence")
            .field("numerator", &self.numerator.to_string())
            .field("denominator", &self.denominator.to_string())
            .field("orientation", &self.orientation)
            .finish()
    }
}

/// Stable identities for arithmetic/order rules whose complete certificate is
/// the target fact plus the recursively checked ordered premise list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithmeticBuiltinRule {
    /// Ordered numeric transitivity. The enclosing result retains the
    /// verifier-owned carrier checks followed by the two ordered premises.
    OrderTransitivity,
    LessEqualFromStrictOrder,
    GreaterEqualFromStrictOrder,
    SubNonnegativeFromLessEqual,
    SubPositiveFromLess,
    AddNonnegative,
    AddPositive,
    AddPositiveLeftStrict,
    AddPositiveRightStrict,
    MulNonnegative,
    MulPositive,
    DivNonnegative,
    DivPositive,
    AddCommonLeftLessEqual,
    SubRightNonnegativeLessEqual,
    AddRightNonnegativeLessEqual,
    AddComponentwiseLessEqual,
    AddCommonLeftLess,
    AddComponentwiseLess,
    AddComponentwiseLessLessEqual,
    AddComponentwiseLessEqualLess,
}

impl ArithmeticBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::OrderTransitivity => "order.transitivity",
            Self::LessEqualFromStrictOrder => "order.less_equal_of_less",
            Self::GreaterEqualFromStrictOrder => "order.greater_equal_of_greater",
            Self::SubNonnegativeFromLessEqual => "order.sub_nonnegative_of_less_equal",
            Self::SubPositiveFromLess => "order.sub_positive_of_less",
            Self::AddNonnegative => "order.add_nonnegative",
            Self::AddPositive => "order.add_positive",
            Self::AddPositiveLeftStrict => "order.add_positive_of_positive_nonnegative",
            Self::AddPositiveRightStrict => "order.add_positive_of_nonnegative_positive",
            Self::MulNonnegative => "order.mul_nonnegative",
            Self::MulPositive => "order.mul_positive",
            Self::DivNonnegative => "order.div_nonnegative",
            Self::DivPositive => "order.div_positive",
            Self::AddCommonLeftLessEqual => "order.add_le_add_left",
            Self::SubRightNonnegativeLessEqual => "order.sub_le_of_le_of_nonnegative",
            Self::AddRightNonnegativeLessEqual => "order.le_add_of_nonnegative_right",
            Self::AddComponentwiseLessEqual => "order.add_le_add",
            Self::AddCommonLeftLess => "order.add_lt_add_left",
            Self::AddComponentwiseLess => "order.add_lt_add",
            Self::AddComponentwiseLessLessEqual => "order.add_lt_add_of_lt_of_le",
            Self::AddComponentwiseLessEqualLess => "order.add_lt_add_of_le_of_lt",
        }
    }
}

/// Stable identities for closure of the integer carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegerMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Mod,
    /// Integer base raised to a checked natural exponent.
    PowNat,
}

/// Stable identities for closure of the natural carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NaturalMembershipClosureBuiltinRule {
    Add,
    Mul,
}

/// Stable identities for closure of the rational carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RationalMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

/// Stable identities for closure of the complex carrier under the migrated
/// proof-carrying binary arithmetic constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComplexArithmeticMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
}

/// Stable identities for closure of the real carrier under arithmetic. The
/// enclosing result retains the checked operand memberships in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealArithmeticMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

/// Stable identities for primitive mathematical-constant memberships that
/// need no premises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeConstantMembershipBuiltinRule {
    ImaginaryUnitInComplex,
    EulerNumberInReal,
    PiInReal,
    EulerNumberInPositiveReal,
    PiInPositiveReal,
    EulerNumberInComplex,
    PiInComplex,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetRelationDualityBuiltinRule {
    SubsetFromSuperset,
    SupersetFromSubset,
    NotSubsetFromNotSuperset,
    NotSupersetFromNotSubset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetBuiltinRule {
    EmptySubset,
    SubsetReflexivity,
    SupersetReflexivity,
    SubsetTransitivity,
    SubsetUnionLeft,
    SubsetUnionRight,
    UnionCommutative,
    UnionAssociative,
    UnionIdempotent,
    UnionEmptyLeft,
    UnionEmptyRight,
    UnionSetMinusDecomposition,
    UnionEqRightOfSubset,
    UnionFinite,
    UnionNonemptyLeft,
    UnionNonemptyRight,
    UnionSubset,
    IntersectCommutative,
    IntersectAssociative,
    IntersectIdempotent,
    IntersectEqLeftOfSubset,
    IntersectEqRightOfSubset,
    IntersectFinite,
    IntersectSubsetLeft,
    IntersectSubsetRight,
    IntersectUnionDistributive,
    IntersectSetMinusSelfEmpty,
    IntersectSetMinusDisjointFromSubset,
    PowerSetFinite,
    PowerSetMembershipOfSubset,
    PowerSetNonempty,
    SetMinusSelfEmpty,
    SetMinusEmptyRight,
    SetMinusEmptyLeft,
    SetMinusFiniteLeft,
    SetMinusInfiniteOfInfiniteFinite,
    SetMinusIntersectDeMorgan,
    SetMinusIntersectSelf,
    SetMinusRecoverSubset,
    SetMinusSubsetLeft,
    SetMinusUnionDeMorgan,
    SubsetEqSetMinusRecovery,
    UnionMembershipLeft,
    UnionMembershipRight,
    IntersectMembershipBoth,
    IntersectNonMembershipLeft,
    IntersectNonMembershipRight,
    SetMinusMembership,
}

impl SetBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::EmptySubset => "set.empty_subset",
            Self::SubsetReflexivity => "set.subset_reflexivity",
            Self::SupersetReflexivity => "set.superset_reflexivity",
            Self::SubsetTransitivity => "set.subset_transitivity",
            Self::SubsetUnionLeft => "set.subset_union_left",
            Self::SubsetUnionRight => "set.subset_union_right",
            Self::UnionCommutative => "set.union_commutative",
            Self::UnionAssociative => "set.union_associative",
            Self::UnionIdempotent => "set.union_idempotent",
            Self::UnionEmptyLeft => "set.union_empty_left",
            Self::UnionEmptyRight => "set.union_empty_right",
            Self::UnionSetMinusDecomposition => "set.union_set_minus_decomposition",
            Self::UnionEqRightOfSubset => "set.union_eq_right_of_subset",
            Self::UnionFinite => "set.union_finite",
            Self::UnionNonemptyLeft => "set.union_nonempty_left",
            Self::UnionNonemptyRight => "set.union_nonempty_right",
            Self::UnionSubset => "set.union_subset",
            Self::IntersectCommutative => "set.intersect_commutative",
            Self::IntersectAssociative => "set.intersect_associative",
            Self::IntersectIdempotent => "set.intersect_idempotent",
            Self::IntersectEqLeftOfSubset => "set.intersect_eq_left_of_subset",
            Self::IntersectEqRightOfSubset => "set.intersect_eq_right_of_subset",
            Self::IntersectFinite => "set.intersect_finite",
            Self::IntersectSubsetLeft => "set.intersect_subset_left",
            Self::IntersectSubsetRight => "set.intersect_subset_right",
            Self::IntersectUnionDistributive => "set.intersect_union_distributive",
            Self::IntersectSetMinusSelfEmpty => "set.intersect_set_minus_self_empty",
            Self::IntersectSetMinusDisjointFromSubset => {
                "set.intersect_set_minus_of_subset_empty"
            }
            Self::PowerSetFinite => "set.power_set_finite",
            Self::PowerSetMembershipOfSubset => "set.power_set_membership_of_subset",
            Self::PowerSetNonempty => "set.power_set_nonempty",
            Self::SetMinusSelfEmpty => "set.set_minus_self_empty",
            Self::SetMinusEmptyRight => "set.set_minus_empty_right",
            Self::SetMinusEmptyLeft => "set.set_minus_empty_left",
            Self::SetMinusFiniteLeft => "set.set_minus_finite_left",
            Self::SetMinusInfiniteOfInfiniteFinite => {
                "set.set_minus_infinite_of_infinite_finite"
            }
            Self::SetMinusIntersectDeMorgan => "set.set_minus_intersect_de_morgan",
            Self::SetMinusIntersectSelf => "set.set_minus_intersect_self",
            Self::SetMinusRecoverSubset => "set.set_minus_recover_subset",
            Self::SetMinusSubsetLeft => "set.set_minus_subset_left",
            Self::SetMinusUnionDeMorgan => "set.set_minus_union_de_morgan",
            Self::SubsetEqSetMinusRecovery => "set.subset_eq_set_minus_recovery",
            Self::UnionMembershipLeft => "set.union_membership_left",
            Self::UnionMembershipRight => "set.union_membership_right",
            Self::IntersectMembershipBoth => "set.intersect_membership",
            Self::IntersectNonMembershipLeft => "set.intersect_nonmembership_left",
            Self::IntersectNonMembershipRight => "set.intersect_nonmembership_right",
            Self::SetMinusMembership => "set.set_minus_membership",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteSetBuiltinRule {
    ListSet,
    Range,
    ClosedRange,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbsoluteValueBuiltinRule {
    Nonnegative,
    SelfLessEqual,
    NegationLessEqual,
    NegativeAbsoluteLessEqual,
    TriangleAdd,
    TriangleSub,
    ReverseTriangleAdd,
    ReverseTriangleSub,
    NonnegativeIdentity,
    NonpositiveNegation,
    Product,
    PositiveFromNonzero,
}

impl AbsoluteValueBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Nonnegative => "order.abs_nonnegative",
            Self::SelfLessEqual => "order.self_le_abs",
            Self::NegationLessEqual => "order.neg_le_abs",
            Self::NegativeAbsoluteLessEqual => "order.neg_abs_le",
            Self::TriangleAdd => "order.abs_add_le",
            Self::TriangleSub => "order.abs_sub_le_sum",
            Self::ReverseTriangleAdd => "order.abs_sub_abs_le_abs_add",
            Self::ReverseTriangleSub => "order.abs_sub_abs_le_abs_sub",
            Self::NonnegativeIdentity => "order.abs_eq_self_of_nonnegative",
            Self::NonpositiveNegation => "order.abs_eq_neg_of_nonpositive",
            Self::Product => "algebra.abs_mul",
            Self::PositiveFromNonzero => "order.abs_positive_of_nonzero",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtremaBuiltinRule {
    MinLessEqualLeft,
    MinLessEqualRight,
    LessEqualMaxLeft,
    LessEqualMaxRight,
    MinEqLeftOfLessEqual,
    MinEqRightOfLessEqual,
    MaxEqLeftOfLessEqual,
    MaxEqRightOfLessEqual,
    MinCommutative,
    MinAssociative,
    MinIdempotent,
    MinAbsorbMaxLeft,
    MaxCommutative,
    MaxAssociative,
    MaxIdempotent,
    MaxAbsorbMinLeft,
    MinMonotone,
    MaxMonotone,
}

impl ExtremaBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::MinLessEqualLeft => "order.min_le_left",
            Self::MinLessEqualRight => "order.min_le_right",
            Self::LessEqualMaxLeft => "order.le_max_left",
            Self::LessEqualMaxRight => "order.le_max_right",
            Self::MinEqLeftOfLessEqual => "order.min_eq_left_of_le",
            Self::MinEqRightOfLessEqual => "order.min_eq_right_of_le",
            Self::MaxEqLeftOfLessEqual => "order.max_eq_left_of_le",
            Self::MaxEqRightOfLessEqual => "order.max_eq_right_of_le",
            Self::MinCommutative => "order.min_commutative",
            Self::MinAssociative => "order.min_associative",
            Self::MinIdempotent => "order.min_idempotent",
            Self::MinAbsorbMaxLeft => "order.min_absorb_max_left",
            Self::MaxCommutative => "order.max_commutative",
            Self::MaxAssociative => "order.max_associative",
            Self::MaxIdempotent => "order.max_idempotent",
            Self::MaxAbsorbMinLeft => "order.max_absorb_min_left",
            Self::MinMonotone => "order.min_monotone",
            Self::MaxMonotone => "order.max_monotone",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregateBuiltinRule {
    SumSingle,
    SumSplitLast,
}

impl AggregateBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::SumSingle => "aggregate.sum_single",
            Self::SumSplitLast => "aggregate.sum_split_last",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonzeroBuiltinRule {
    Mul,
}

impl NonzeroBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Mul => "nonzero.mul",
        }
    }
}

/// Checked definition-elimination certificate for an existential hidden
/// behind one concrete proposition call. The enclosing result is the
/// instantiated existential and has exactly one child: a proof of `source`.
#[derive(Clone)]
pub struct DefinitionProjectionBuiltinRuleEvidence {
    pub fact: NormalAtomicFact,
    pub definition: DefPropStmt,
}

/// Exact constructor certificate for membership in a literal set builder.
/// Child results are ordered as base membership followed by the instantiated
/// defining facts in source order. The builder is recovered from
/// `expected_target`.
#[derive(Clone)]
pub struct SetBuilderMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_premises: Vec<Fact>,
}

/// Exact extensional certificate for membership in a Litex function space.
/// The enclosing result has exactly one child: the checked pointwise `forall`
/// proposition retained in `expected_pointwise`. The element and function
/// space are recovered from `expected_target`.
#[derive(Clone)]
pub struct FunctionSetMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_pointwise: Fact,
}

/// Exact constructor certificate for a literal tuple in a literal Cartesian
/// product. The verifier retains coordinate memberships in source order; for
/// arity greater than one they are checked by one conjunction child Result.
#[derive(Clone)]
pub struct TupleCartesianMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_coordinate_memberships: Vec<Fact>,
}

/// Exact monotonicity certificate for two inclusive integer-range sums. The
/// verifier retains the endpoint equalities followed by one binder-owning
/// pointwise `forall` Result. The compiler may support only a reviewed subset
/// of aggregate carriers, but it must never reconstruct the lost binder from
/// the target expression.
#[derive(Clone)]
pub struct IntegerRangeSumPointwiseOrderBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_start_equality: Fact,
    pub expected_end_equality: Fact,
    pub expected_pointwise: Fact,
}

/// Exact constructor certificate for a refined standard numeric set. Children
/// are ordered as the native base-carrier membership followed by the defining
/// sign/nonzero predicate. The numeric set is recovered from `expected_target`.
#[derive(Clone)]
pub struct RefinedNumericMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_premises: Vec<Fact>,
}

/// A closed numeric expression was recursively evaluated and the resulting
/// number was checked against one standard numeric set.  The source expression
/// remains part of `expected_target`; `evaluation` records how it reached the
/// normalized value used by the membership decision.
#[derive(Clone)]
pub struct ClosedNumericMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
    pub evaluation: SuccessEvaluateObjResult,
}

/// Zero-premise equality certificate whose two source objects are exactly the
/// same object after parser-owned binding identity is taken into account.
#[derive(Clone)]
pub struct ObjectReflexivityBuiltinRuleEvidence {
    pub expected_target: Fact,
}

/// Zero-premise equality certificate for two closed numeric expressions. Both
/// recursive evaluation trees are retained so a backend never has to infer
/// the normal form from a diagnostic label.
#[derive(Clone)]
pub struct RationalNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub left_evaluation: SuccessEvaluateObjResult,
    pub right_evaluation: SuccessEvaluateObjResult,
}

/// Equality certificate selected only after exact bounded polynomial/rational
/// normalization with the relation `i * i = -1`. Every denominator or
/// negative-power base needed by that normalization is retained as an exact
/// nonzero premise; an empty list records a genuinely zero-premise identity.
#[derive(Clone)]
pub struct ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_nonzero_premises: Vec<Fact>,
}

/// One exact named-function unfolding used below a reviewed structural
/// equality context. The defining equality is retained by `FactId`; the
/// application and its substituted body make the reduction independently
/// replayable after the verifier Runtime has been dropped.
#[derive(Clone)]
pub struct NestedCheckedFunctionDefinitionReductionEvidence {
    pub definition_object: Obj,
    pub defining_equality: Fact,
    pub defining_equality_fact_id: FactId,
    pub application: Obj,
    pub reduced: Obj,
}

/// Equality obtained only by applying the retained named-function reductions
/// below matching object constructors. No calculation or ambient equality
/// search is hidden in this certificate.
#[derive(Clone)]
pub struct StructuralDefinitionCongruenceBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub reductions: Vec<NestedCheckedFunctionDefinitionReductionEvidence>,
}

/// Equality obtained by applying reviewed addition congruence to exact child
/// Results. Identical leaves are reflexive; every non-identical leaf is
/// retained as one ordered child Result instead of being rediscovered from a
/// verifier environment after compilation.
#[derive(Clone)]
pub struct StructuralKnownEqualityCongruenceBuiltinRuleEvidence {
    pub expected_target: Fact,
}

/// A zero-premise identity in the deliberately small integral-polynomial
/// fragment: atoms and integer literals closed under `+`, `-`, `*`, and
/// nonnegative literal powers. Both verifier and compiler independently
/// recheck the exact target against that fragment.
#[derive(Clone)]
pub struct IntegralPolynomialNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
}

/// A standard carrier is inhabited by its reviewed canonical witness. The
/// target is retained explicitly so consumers never recover this rule from a
/// diagnostic label.
#[derive(Clone)]
pub struct StandardSetNonemptyBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
}

impl fmt::Debug for StandardSetNonemptyBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("StandardSetNonemptyBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set)
            .finish()
    }
}

impl fmt::Debug for NestedCheckedFunctionDefinitionReductionEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("NestedCheckedFunctionDefinitionReductionEvidence")
            .field("definition_object", &self.definition_object.to_string())
            .field("defining_equality", &self.defining_equality.to_string())
            .field("defining_equality_fact_id", &self.defining_equality_fact_id)
            .field("application", &self.application.to_string())
            .field("reduced", &self.reduced.to_string())
            .finish()
    }
}

impl fmt::Debug for StructuralDefinitionCongruenceBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("StructuralDefinitionCongruenceBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("reductions", &self.reductions)
            .finish()
    }
}

impl fmt::Debug for StructuralKnownEqualityCongruenceBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("StructuralKnownEqualityCongruenceBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

impl fmt::Debug for IntegralPolynomialNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("IntegralPolynomialNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

/// The negative counterpart of `ClosedNumericMembershipBuiltinRuleEvidence`.
#[derive(Clone)]
pub struct ClosedNumericNonmembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
    pub evaluation: SuccessEvaluateObjResult,
}

/// A closed literal numeric comparison checked by the verifier's evaluator.
/// The Lean carrier remains contextual (for example `0 < 1` may be needed in
/// an `ℝ` proof), so the certificate freezes the proposition without choosing a
/// different source-level numeric set.
#[derive(Clone)]
pub struct ClosedNumericComparisonBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub left_evaluation: SuccessEvaluateObjResult,
    pub right_evaluation: SuccessEvaluateObjResult,
}

/// A weak order on one object, or the negation of a strict order on that same
/// object, discharged by reflexivity/irreflexivity rather than calculation.
///
/// Keeping this separate from `ClosedNumericComparisonBuiltinRuleEvidence`
/// matters for compositional consumers: `x <= x` is valid in a local binder
/// environment even though `x` is not a closed numeric expression.
#[derive(Clone)]
pub struct OrderReflexivityBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub repeated_object: Obj,
}

/// Compatibility evidence for a comparison decided only after `Runtime`
/// substituted known object values. The resolved operands are retained so the
/// execution Result says what was compared, but a standalone compiler must
/// reject this route until the substitutions themselves carry cited FactIds.
#[derive(Clone)]
pub struct RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub normalized_left: Obj,
    pub normalized_right: Obj,
}

/// Exact use of a previously proved and registered reflexivity theorem for a
/// user-defined binary predicate.
#[derive(Clone)]
pub struct RegisteredReflexivePredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
}

/// Exact use of a previously proved and registered permutation theorem for a
/// user-defined predicate. The enclosing builtin proof owns exactly one child
/// Result proving `expected_alternate`; `gather` records how the target's
/// arguments were reordered to obtain that premise.
#[derive(Clone)]
pub struct RegisteredSymmetricPredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
    pub gather: Vec<usize>,
    pub expected_alternate: Fact,
}

/// Exact use of a previously proved and registered antisymmetry theorem for a
/// user-defined binary predicate. The enclosing builtin proof owns the two
/// ordered predicate-premise child Results.
#[derive(Clone)]
pub struct RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
}

/// Exact dependent-elimination certificate for membership of a checked
/// function application in its instantiated defined return set. The sole
/// child proves that the application head belongs to the function space frozen
/// in `expected_head_membership`.
#[derive(Clone)]
pub struct FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub typed_return_set: Obj,
    pub expected_target: Fact,
    pub expected_head_membership: Fact,
}

/// Exact carrier certificate for a native matrix expression. The enclosing
/// fact's recursive well-definedness result owns the operand carrier and
/// dimension checks; this payload records the matrix type computed by that
/// checked constructor and the membership proposition it discharges.
#[derive(Clone)]
pub struct MatrixExpressionMembershipBuiltinRuleEvidence {
    pub inferred_matrix_set: MatrixSet,
    pub expected_target: Fact,
}

impl fmt::Debug for MatrixExpressionMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("MatrixExpressionMembershipBuiltinRuleEvidence")
            .field(
                "inferred_matrix_set",
                &Obj::from(self.inferred_matrix_set.clone()).to_string(),
            )
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

/// Exact direct-equality path selected while checking one equality-class
/// result. Every step cites the environment-stored fact that justified it.
#[derive(Clone)]
pub struct KnownEqualityBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub steps: Vec<KnownEqualityBuiltinRuleStep>,
}

impl KnownEqualityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, steps: Vec<KnownEqualityBuiltinRuleStep>) -> Self {
        Self {
            expected_target,
            steps,
        }
    }
}

impl fmt::Debug for KnownEqualityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("KnownEqualityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("steps", &self.steps)
            .finish()
    }
}

#[derive(Clone)]
pub struct KnownEqualityBuiltinRuleStep {
    pub from: Obj,
    pub to: Obj,
    pub equality: EqualFact,
    pub source_fact_id: FactId,
}

impl KnownEqualityBuiltinRuleStep {
    pub fn new(from: Obj, to: Obj, equality: EqualFact, source_fact_id: FactId) -> Self {
        Self {
            from,
            to,
            equality,
            source_fact_id,
        }
    }
}

impl fmt::Debug for KnownEqualityBuiltinRuleStep {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("KnownEqualityBuiltinRuleStep")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("equality", &self.equality.to_string())
            .field("source_fact_id", &self.source_fact_id)
            .finish()
    }
}

impl FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub fn new(
        typed_return_set: Obj,
        expected_target: Fact,
        expected_head_membership: Fact,
    ) -> Self {
        Self {
            typed_return_set,
            expected_target,
            expected_head_membership,
        }
    }
}

impl fmt::Debug for FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionApplicationReturnMembershipBuiltinRuleEvidence")
            .field("typed_return_set", &self.typed_return_set.to_string())
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_head_membership",
                &self.expected_head_membership.to_string(),
            )
            .finish()
    }
}

impl ClosedNumericComparisonBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        left_evaluation: SuccessEvaluateObjResult,
        right_evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            left_evaluation,
            right_evaluation,
        }
    }
}

impl OrderReflexivityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, repeated_object: Obj) -> Self {
        Self {
            expected_target,
            repeated_object,
        }
    }
}

impl RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, normalized_left: Obj, normalized_right: Obj) -> Self {
        Self {
            expected_target,
            normalized_left,
            normalized_right,
        }
    }
}

impl RegisteredReflexivePredicateBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, predicate_name: String) -> Self {
        Self {
            expected_target,
            predicate_name,
        }
    }
}

impl RegisteredSymmetricPredicateBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        predicate_name: String,
        gather: Vec<usize>,
        expected_alternate: Fact,
    ) -> Self {
        Self {
            expected_target,
            predicate_name,
            gather,
            expected_alternate,
        }
    }
}

impl RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, predicate_name: String) -> Self {
        Self {
            expected_target,
            predicate_name,
        }
    }
}

impl ClosedNumericMembershipBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        target_set: StandardSet,
        evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            target_set,
            evaluation,
        }
    }
}

impl ObjectReflexivityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact) -> Self {
        Self { expected_target }
    }
}

impl RationalNormalizationBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        left_evaluation: SuccessEvaluateObjResult,
        right_evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            left_evaluation,
            right_evaluation,
        }
    }
}

impl ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_nonzero_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_nonzero_premises,
        }
    }
}

impl fmt::Debug for ClosedNumericMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set.to_string())
            .field("evaluation", &self.evaluation)
            .finish()
    }
}

impl fmt::Debug for ObjectReflexivityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ObjectReflexivityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

impl fmt::Debug for RationalNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RationalNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("left_evaluation", &self.left_evaluation)
            .field("right_evaluation", &self.right_evaluation)
            .finish()
    }
}

impl fmt::Debug for ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ComplexAlgebraicNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_nonzero_premises",
                &self
                    .expected_nonzero_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl ClosedNumericNonmembershipBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        target_set: StandardSet,
        evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            target_set,
            evaluation,
        }
    }
}

impl fmt::Debug for ClosedNumericNonmembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericNonmembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set.to_string())
            .field("evaluation", &self.evaluation)
            .finish()
    }
}

impl fmt::Debug for ClosedNumericComparisonBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericComparisonBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("left_evaluation", &self.left_evaluation)
            .field("right_evaluation", &self.right_evaluation)
            .finish()
    }
}

impl fmt::Debug for OrderReflexivityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("OrderReflexivityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("repeated_object", &self.repeated_object.to_string())
            .finish()
    }
}

impl fmt::Debug for RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RuntimeResolvedNumericComparisonBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("normalized_left", &self.normalized_left.to_string())
            .field("normalized_right", &self.normalized_right.to_string())
            .finish()
    }
}

impl fmt::Debug for RegisteredReflexivePredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredReflexivePredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .finish()
    }
}

impl fmt::Debug for RegisteredSymmetricPredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredSymmetricPredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .field("gather", &self.gather)
            .field("expected_alternate", &self.expected_alternate.to_string())
            .finish()
    }
}

impl fmt::Debug for RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredAntisymmetricPredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .finish()
    }
}

impl RefinedNumericMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for RefinedNumericMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RefinedNumericMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_premises",
                &self
                    .expected_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl FunctionSetMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_pointwise: Fact) -> Self {
        Self {
            expected_target,
            expected_pointwise,
        }
    }
}

impl TupleCartesianMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_coordinate_memberships: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_coordinate_memberships,
        }
    }
}

impl IntegerRangeSumPointwiseOrderBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        expected_start_equality: Fact,
        expected_end_equality: Fact,
        expected_pointwise: Fact,
    ) -> Self {
        Self {
            expected_target,
            expected_start_equality,
            expected_end_equality,
            expected_pointwise,
        }
    }
}

impl fmt::Debug for IntegerRangeSumPointwiseOrderBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("IntegerRangeSumPointwiseOrderBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_start_equality",
                &self.expected_start_equality.to_string(),
            )
            .field(
                "expected_end_equality",
                &self.expected_end_equality.to_string(),
            )
            .field("expected_pointwise", &self.expected_pointwise.to_string())
            .finish()
    }
}

impl fmt::Debug for TupleCartesianMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("TupleCartesianMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_coordinate_memberships",
                &self
                    .expected_coordinate_memberships
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl fmt::Debug for FunctionSetMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionSetMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("expected_pointwise", &self.expected_pointwise.to_string())
            .finish()
    }
}

impl SetBuilderMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for SetBuilderMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("SetBuilderMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_premises",
                &self
                    .expected_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl DefinitionProjectionBuiltinRuleEvidence {
    pub fn new(fact: NormalAtomicFact, definition: DefPropStmt) -> Self {
        Self { fact, definition }
    }
}

impl fmt::Debug for DefinitionProjectionBuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("DefinitionProjectionBuiltinRuleEvidence")
            .field("source", &self.fact.to_string())
            .field("definition", &self.definition.name)
            .finish()
    }
}

#[derive(Clone)]
pub enum BuiltinRuleEvidence {
    /// A typed verifier-owned rule that deliberately has no reviewed ToLean
    /// mapping yet. The exact enum variant, rather than a diagnostic string,
    /// is the rule identity.
    Uncatalogued(UncataloguedBuiltinRule),
    DefinitionProjection(DefinitionProjectionBuiltinRuleEvidence),
    SetBuilderMembership(SetBuilderMembershipBuiltinRuleEvidence),
    FunctionSetMembership(FunctionSetMembershipBuiltinRuleEvidence),
    TupleCartesianMembership(TupleCartesianMembershipBuiltinRuleEvidence),
    IntegerRangeSumPointwiseOrder(IntegerRangeSumPointwiseOrderBuiltinRuleEvidence),
    RefinedNumericMembership(RefinedNumericMembershipBuiltinRuleEvidence),
    ClosedNumericMembership(ClosedNumericMembershipBuiltinRuleEvidence),
    ClosedNumericNonmembership(ClosedNumericNonmembershipBuiltinRuleEvidence),
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleEvidence),
    OrderReflexivity(OrderReflexivityBuiltinRuleEvidence),
    RuntimeResolvedNumericComparison(RuntimeResolvedNumericComparisonBuiltinRuleEvidence),
    RegisteredReflexivePredicate(RegisteredReflexivePredicateBuiltinRuleEvidence),
    RegisteredSymmetricPredicate(RegisteredSymmetricPredicateBuiltinRuleEvidence),
    RegisteredAntisymmetricPredicate(RegisteredAntisymmetricPredicateBuiltinRuleEvidence),
    ObjectReflexivity(ObjectReflexivityBuiltinRuleEvidence),
    RationalNormalization(RationalNormalizationBuiltinRuleEvidence),
    ComplexAlgebraicNormalization(ComplexAlgebraicNormalizationBuiltinRuleEvidence),
    StructuralDefinitionCongruence(StructuralDefinitionCongruenceBuiltinRuleEvidence),
    StructuralKnownEqualityCongruence(StructuralKnownEqualityCongruenceBuiltinRuleEvidence),
    IntegralPolynomialNormalization(IntegralPolynomialNormalizationBuiltinRuleEvidence),
    StandardSetNonempty(StandardSetNonemptyBuiltinRuleEvidence),
    /// A nonempty finite set literal is inhabited by the first singleton
    /// carrier in its exact coproduct encoding.
    LiteralSetNonempty,
    /// A predicate-defined set is contained in its exact base carrier.
    SetBuilderSubsetBase,
    DisjunctionIntroduction(DisjunctionIntroductionBuiltinRuleEvidence),
    FunctionApplicationReturnMembership(FunctionApplicationReturnMembershipBuiltinRuleEvidence),
    MatrixExpressionMembership(MatrixExpressionMembershipBuiltinRuleEvidence),
    KnownEqualityPath(KnownEqualityBuiltinRuleEvidence),
    DivNotEqualZero(DivNotEqualZeroBuiltinRuleEvidence),
    Arithmetic(ArithmeticBuiltinRule),
    IntegerMembershipClosure(IntegerMembershipClosureBuiltinRule),
    /// An inclusive integer-range sum whose checked iterand returns exactly
    /// `Z` belongs to the exact `Z` carrier.
    IntegerRangeSumMembership,
    NaturalMembershipClosure(NaturalMembershipClosureBuiltinRule),
    RationalMembershipClosure(RationalMembershipClosureBuiltinRule),
    ComplexArithmeticMembershipClosure(ComplexArithmeticMembershipClosureBuiltinRule),
    RealArithmeticMembershipClosure(RealArithmeticMembershipClosureBuiltinRule),
    NativeConstantMembership(NativeConstantMembershipBuiltinRule),
    NotEqualSymmetry,
    /// Two checked real-carrier premises followed by one strict comparison
    /// between the target operands prove their inequality.
    NotEqualFromStrictOrder,
    SetRelationDuality(SetRelationDualityBuiltinRule),
    Set(SetBuiltinRule),
    FiniteSet(FiniteSetBuiltinRule),
    ListSetMembership(ListSetMembershipBuiltinRuleEvidence),
    TupleLiteralShape,
    AbsoluteValue(AbsoluteValueBuiltinRule),
    Extrema(ExtremaBuiltinRule),
    Aggregate(AggregateBuiltinRule),
    Nonzero(NonzeroBuiltinRule),
    PrimeU64Reflection,
    CoprimeNaturalReflection,
    /// Membership in one standard numeric set is projected through Litex's
    /// centralized standard-set hierarchy. The enclosing result has exactly
    /// one child: the checked source membership fact.
    StandardSetMembershipProjection,
    /// One fixed inclusion in Litex's standard numeric-set hierarchy. The
    /// target subset fact itself retains the exact source and target sets.
    StandardSetSubset,
    /// A literal finite-set inclusion whose ordered subgoals prove membership
    /// of every literal item in the retained target set.
    LiteralSetSubset,
}

impl fmt::Debug for BuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BuiltinRuleEvidence::Uncatalogued(rule) => {
                f.debug_tuple("Uncatalogued").field(rule).finish()
            }
            BuiltinRuleEvidence::DefinitionProjection(evidence) => f
                .debug_tuple("DefinitionProjection")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::SetBuilderMembership(evidence) => f
                .debug_tuple("SetBuilderMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::FunctionSetMembership(evidence) => f
                .debug_tuple("FunctionSetMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::TupleCartesianMembership(evidence) => f
                .debug_tuple("TupleCartesianMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::IntegerRangeSumPointwiseOrder(evidence) => f
                .debug_tuple("IntegerRangeSumPointwiseOrder")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RefinedNumericMembership(evidence) => f
                .debug_tuple("RefinedNumericMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ClosedNumericMembership(evidence) => f
                .debug_tuple("ClosedNumericMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ClosedNumericNonmembership(evidence) => f
                .debug_tuple("ClosedNumericNonmembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ClosedNumericComparison(evidence) => f
                .debug_tuple("ClosedNumericComparison")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::OrderReflexivity(evidence) => {
                f.debug_tuple("OrderReflexivity").field(evidence).finish()
            }
            BuiltinRuleEvidence::RuntimeResolvedNumericComparison(evidence) => f
                .debug_tuple("RuntimeResolvedNumericComparison")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence) => f
                .debug_tuple("RegisteredReflexivePredicate")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence) => f
                .debug_tuple("RegisteredSymmetricPredicate")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence) => f
                .debug_tuple("RegisteredAntisymmetricPredicate")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ObjectReflexivity(evidence) => {
                f.debug_tuple("ObjectReflexivity").field(evidence).finish()
            }
            BuiltinRuleEvidence::RationalNormalization(evidence) => f
                .debug_tuple("RationalNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence) => f
                .debug_tuple("ComplexAlgebraicNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::StructuralDefinitionCongruence(evidence) => f
                .debug_tuple("StructuralDefinitionCongruence")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::StructuralKnownEqualityCongruence(evidence) => f
                .debug_tuple("StructuralKnownEqualityCongruence")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::IntegralPolynomialNormalization(evidence) => f
                .debug_tuple("IntegralPolynomialNormalization")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::StandardSetNonempty(evidence) => f
                .debug_tuple("StandardSetNonempty")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::LiteralSetNonempty => f.write_str("LiteralSetNonempty"),
            BuiltinRuleEvidence::SetBuilderSubsetBase => f.write_str("SetBuilderSubsetBase"),
            BuiltinRuleEvidence::DisjunctionIntroduction(evidence) => f
                .debug_tuple("DisjunctionIntroduction")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence) => f
                .debug_tuple("FunctionApplicationReturnMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::MatrixExpressionMembership(evidence) => f
                .debug_tuple("MatrixExpressionMembership")
                .field(evidence)
                .finish(),
            BuiltinRuleEvidence::KnownEqualityPath(evidence) => {
                f.debug_tuple("KnownEqualityPath").field(evidence).finish()
            }
            BuiltinRuleEvidence::DivNotEqualZero(evidence) => {
                f.debug_tuple("DivNotEqualZero").field(evidence).finish()
            }
            BuiltinRuleEvidence::Arithmetic(rule) => {
                f.debug_tuple("Arithmetic").field(rule).finish()
            }
            BuiltinRuleEvidence::IntegerMembershipClosure(rule) => f
                .debug_tuple("IntegerMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::IntegerRangeSumMembership => {
                f.write_str("IntegerRangeSumMembership")
            }
            BuiltinRuleEvidence::NaturalMembershipClosure(rule) => f
                .debug_tuple("NaturalMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::RationalMembershipClosure(rule) => f
                .debug_tuple("RationalMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule) => f
                .debug_tuple("ComplexArithmeticMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule) => f
                .debug_tuple("RealArithmeticMembershipClosure")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::NativeConstantMembership(rule) => f
                .debug_tuple("NativeConstantMembership")
                .field(rule)
                .finish(),
            BuiltinRuleEvidence::NotEqualSymmetry => f.write_str("NotEqualSymmetry"),
            BuiltinRuleEvidence::NotEqualFromStrictOrder => f.write_str("NotEqualFromStrictOrder"),
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                f.debug_tuple("SetRelationDuality").field(rule).finish()
            }
            BuiltinRuleEvidence::Set(rule) => f.debug_tuple("Set").field(rule).finish(),
            BuiltinRuleEvidence::FiniteSet(rule) => f.debug_tuple("FiniteSet").field(rule).finish(),
            BuiltinRuleEvidence::ListSetMembership(evidence) => {
                f.debug_tuple("ListSetMembership").field(evidence).finish()
            }
            BuiltinRuleEvidence::TupleLiteralShape => f.write_str("TupleLiteralShape"),
            BuiltinRuleEvidence::AbsoluteValue(rule) => {
                f.debug_tuple("AbsoluteValue").field(rule).finish()
            }
            BuiltinRuleEvidence::Extrema(rule) => {
                f.debug_tuple("Extrema").field(rule).finish()
            }
            BuiltinRuleEvidence::Aggregate(rule) => {
                f.debug_tuple("Aggregate").field(rule).finish()
            }
            BuiltinRuleEvidence::Nonzero(rule) => {
                f.debug_tuple("Nonzero").field(rule).finish()
            }
            BuiltinRuleEvidence::PrimeU64Reflection => f.write_str("PrimeU64Reflection"),
            BuiltinRuleEvidence::CoprimeNaturalReflection => {
                f.write_str("CoprimeNaturalReflection")
            }
            BuiltinRuleEvidence::StandardSetMembershipProjection => {
                f.write_str("StandardSetMembershipProjection")
            }
            BuiltinRuleEvidence::StandardSetSubset => f.write_str("StandardSetSubset"),
            BuiltinRuleEvidence::LiteralSetSubset => f.write_str("LiteralSetSubset"),
        }
    }
}
