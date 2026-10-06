//! Explain + cite for `LessEqualFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{
    FromKnownGreaterEqualBuiltinRuleProof,
LessEqualFactSearchProofByBuiltinRule,
    AbsLeFromSymmetricBoundsBuiltinRuleProof,
    AbsLeImpliesNegUpperBuiltinRuleProof,
    AbsLeImpliesUpperBuiltinRuleProof,
    AbsNonnegativeBuiltinRuleProof,
    AbsReverseTriangleAddBuiltinRuleProof,
    AbsReverseTriangleSubBuiltinRuleProof,
    AbsSelfLowerBuiltinRuleProof,
    AbsSelfUpperBuiltinRuleProof,
    AbsTriangleInequalityBuiltinRuleProof,
    AddLeftCongruenceBuiltinRuleProof,
    AddLeftNonnegativeBuiltinRuleProof,
    AddRightCongruenceBuiltinRuleProof,
    AddRightNonnegativeBuiltinRuleProof,
    ArccosPrincipalLowerBoundBuiltinRuleProof,
    ArccosPrincipalUpperBoundBuiltinRuleProof,
    ArcsinPrincipalLowerBoundBuiltinRuleProof,
    ArcsinPrincipalUpperBoundBuiltinRuleProof,
    ClosedNumericComparisonBuiltinRuleProof,
    DivMonotoneWeakSameNegDivisorBuiltinRuleProof,
    DivMonotoneWeakSamePosDivisorBuiltinRuleProof,
    EvenPowNonnegativeBuiltinRuleProof,
    FiniteSetMaxMemberLeBuiltinRuleProof,
    PositiveCommonDivisorLeGcdBuiltinRuleProof,
    FiniteSetMinMemberLeBuiltinRuleProof,
    FiniteSetSizeAtLeastOneLeBuiltinRuleProof,
    FiniteSetSizeNonnegativeLeBuiltinRuleProof,
    FiniteSetSizeSubsetLeBuiltinRuleProof,
    FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof,
    FiniteSetSizeUnionLeSumBuiltinRuleProof,
    FromKnownInPositiveNaturalBuiltinRuleProof,
    FromKnownLessBuiltinRuleProof,
    IntegerAdjacencyLeBuiltinRuleProof,
    IntegerDiffAtLeastOneLeBuiltinRuleProof,
    IntegerPredecessorLeBuiltinRuleProof,
    IntegerSuccessorLeBuiltinRuleProof,
    LessEqualFromNonnegDifferenceBuiltinRuleProof,

    LessEqualFromPosDenomQuotientBoundBuiltinRuleProof,
    LessEqualFromPosDivProductBoundBuiltinRuleProof,
    LessEqualTransitivityBuiltinRuleProof,
    LogOrderPreservingWeakBuiltinRuleProof,
    ModRemainderNonnegativeBuiltinRuleProof,
    MulLeftNonnegativeMonotoneBuiltinRuleProof,
    MulRightNonnegativeMonotoneBuiltinRuleProof,
    NonnegDifferenceFromLessEqualBuiltinRuleProof,
    NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof,
    NumericLowerBoundWeakenLeBuiltinRuleProof,
    NumericUpperBoundWeakenLeBuiltinRuleProof,
    OrderReflexivityBuiltinRuleProof,
    PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof,
    PowNonnegFromPositiveBaseBuiltinRuleProof,
    ProductOfNonnegativesBuiltinRuleProof,
    SqrtMonotoneNondecreasingBuiltinRuleProof,
    SqrtNonnegativeBuiltinRuleProof,
    SubNonnegativeBuiltinRuleProof,
    SumOfNonnegativesBuiltinRuleProof,
    UnitCircleLowerBoundBuiltinRuleProof,
    UnitCircleUpperBoundBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessEqualBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromNegativeLiteralBoundBuiltinRuleProof;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl LessEqualFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_en(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_en(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_en(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_en(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_en(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_en(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_en(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_en(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_en(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_en(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_en(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_en(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_en(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_en(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_en(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_en(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_en(),

            Self::ClosedSubtractionBound(_) => text("Subtract from a stored numeric bound", "The stored upper or lower bound remains sufficient after subtracting the closed constant"),
            Self::ComplexModulusNonnegative => text("Nonnegative complex modulus", "The principal complex modulus is nonnegative"),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_en(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_en(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_en(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_en(),
            Self::FromKnownLess(p) => p.rule_name_and_message_en(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_en(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_en(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_en(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_en(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_en(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_en(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_en(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_en(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_en(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_en(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_en(),
            Self::SubNonnegative(p) => p.rule_name_and_message_en(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_en(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_en(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_en(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_en(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_en(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_en(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_en(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_en(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_en(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_en(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_en(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_en(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_en(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_en(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_en(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_en(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_en(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_en(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_en(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_en(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_en(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_en(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_en(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_en(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_en(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_en(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_en(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_en(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_en(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_en(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_en(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_en(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_en(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_en(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_en(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_en(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_en(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_en(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_en(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_en(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_en(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_zh(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_zh(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_zh(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_zh(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_zh(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_zh(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_zh(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_zh(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_zh(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_zh(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_zh(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_zh(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_zh(),

            Self::ClosedSubtractionBound(_) => text(
                "从已有数值界减去常数",
                "已有上界或下界减去闭式常数后满足目标弱序界",
            ),
            Self::ComplexModulusNonnegative => text(
                "复数模长非负",
                "复数模长取非负主根",
            ),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_zh(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_zh(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_zh(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_zh(),
            Self::FromKnownLess(p) => p.rule_name_and_message_zh(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_zh(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_zh(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_zh(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_zh(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_zh(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_zh(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_zh(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_zh(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_zh(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_zh(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_zh(),
            Self::SubNonnegative(p) => p.rule_name_and_message_zh(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_zh(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_zh(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_zh(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_zh(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_zh(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_zh(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_zh(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_zh(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_zh(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_zh(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_zh(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_zh(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_zh(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_zh(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_zh(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_zh(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_zh(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_zh(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_zh(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_zh(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_zh(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_zh(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_zh(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_zh(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_zh(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_zh(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_zh(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_zh(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_zh(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_zh(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_zh(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_zh(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_zh(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_zh(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_zh(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_zh(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_zh(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_zh(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_zh(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh_hant(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh_hant(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh_hant(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_zh_hant(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_zh_hant(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_zh_hant(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_zh_hant(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_zh_hant(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_zh_hant(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_zh_hant(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_zh_hant(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_zh_hant(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_zh_hant(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_zh_hant(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_zh_hant(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_zh_hant(),

            Self::ClosedSubtractionBound(_) => text(
                "從已有數值界減去常數",
                "已有上界或下界減去封閉常數後仍足以滿足目標",
            ),
            Self::ComplexModulusNonnegative => text(
                "複數模長非負",
                "複數模長取非負主根",
            ),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_zh_hant(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_zh_hant(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownLess(p) => p.rule_name_and_message_zh_hant(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_zh_hant(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_zh_hant(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_zh_hant(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_zh_hant(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_zh_hant(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_zh_hant(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_zh_hant(),
            Self::SubNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_zh_hant(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_zh_hant(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_zh_hant(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_zh_hant(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_zh_hant(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_zh_hant(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_zh_hant(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_zh_hant(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_zh_hant(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_zh_hant(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_zh_hant(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_zh_hant(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_zh_hant(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_zh_hant(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_zh_hant(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_zh_hant(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_zh_hant(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_zh_hant(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_zh_hant(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_zh_hant(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_zh_hant(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_zh_hant(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_zh_hant(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_zh_hant(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_zh_hant(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_zh_hant(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_zh_hant(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_zh_hant(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_fr(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_fr(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_fr(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_fr(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_fr(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_fr(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_fr(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_fr(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_fr(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_fr(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_fr(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_fr(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_fr(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_fr(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_fr(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_fr(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_fr(),

            Self::ClosedSubtractionBound(_) => text("Soustraction d'une borne numérique stockée", "La borne supérieure ou inférieure stockée reste suffisante après soustraction de la constante fermée"),
            Self::ComplexModulusNonnegative => text("Module complexe non négatif", "Le module complexe principal est non négatif"),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_fr(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_fr(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_fr(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_fr(),
            Self::FromKnownLess(p) => p.rule_name_and_message_fr(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_fr(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_fr(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_fr(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_fr(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_fr(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_fr(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_fr(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_fr(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_fr(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_fr(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_fr(),
            Self::SubNonnegative(p) => p.rule_name_and_message_fr(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_fr(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_fr(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_fr(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_fr(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_fr(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_fr(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_fr(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_fr(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_fr(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_fr(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_fr(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_fr(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_fr(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_fr(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_fr(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_fr(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_fr(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_fr(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_fr(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_fr(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_fr(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_fr(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_fr(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_fr(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_fr(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_fr(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_fr(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_fr(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_fr(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_fr(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_fr(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_fr(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_fr(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_fr(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_fr(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_fr(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_fr(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_fr(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_fr(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ru(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ru(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ru(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ru(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_ru(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_ru(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_ru(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_ru(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_ru(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_ru(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_ru(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_ru(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_ru(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_ru(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_ru(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_ru(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_ru(),

            Self::ClosedSubtractionBound(_) => text("Вычитание из сохранённой числовой границы", "Сохранённая верхняя или нижняя граница остаётся достаточной после вычитания замкнутой константы"),
            Self::ComplexModulusNonnegative => text("Неотрицательный комплексный модуль", "Главный комплексный модуль неотрицателен"),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_ru(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ru(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ru(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ru(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ru(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_ru(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_ru(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_ru(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_ru(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_ru(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_ru(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_ru(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_ru(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_ru(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_ru(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_ru(),
            Self::SubNonnegative(p) => p.rule_name_and_message_ru(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_ru(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_ru(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_ru(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_ru(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_ru(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_ru(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_ru(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_ru(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_ru(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_ru(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_ru(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_ru(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_ru(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_ru(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_ru(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_ru(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_ru(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ru(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_ru(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_ru(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_ru(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_ru(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_ru(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_ru(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_ru(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_ru(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_ru(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_ru(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_ru(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_ru(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_ru(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_ru(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_ru(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_ru(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_ru(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_ru(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_ru(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_ru(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ru(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_es(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_es(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_es(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_es(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_es(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_es(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_es(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_es(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_es(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_es(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_es(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_es(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_es(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_es(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_es(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_es(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_es(),

            Self::ClosedSubtractionBound(_) => text("Resta de una cota numérica almacenada", "La cota superior o inferior almacenada sigue siendo suficiente al restar la constante cerrada"),
            Self::ComplexModulusNonnegative => text("Módulo complejo no negativo", "El módulo complejo principal es no negativo"),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_es(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_es(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_es(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_es(),
            Self::FromKnownLess(p) => p.rule_name_and_message_es(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_es(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_es(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_es(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_es(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_es(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_es(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_es(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_es(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_es(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_es(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_es(),
            Self::SubNonnegative(p) => p.rule_name_and_message_es(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_es(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_es(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_es(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_es(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_es(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_es(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_es(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_es(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_es(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_es(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_es(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_es(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_es(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_es(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_es(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_es(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_es(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_es(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_es(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_es(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_es(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_es(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_es(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_es(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_es(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_es(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_es(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_es(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_es(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_es(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_es(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_es(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_es(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_es(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_es(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_es(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_es(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_es(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_es(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_es(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_es(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ar(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ar(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ar(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ar(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_ar(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_ar(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_ar(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_ar(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_ar(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_ar(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_ar(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_ar(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_ar(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_ar(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_ar(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_ar(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_ar(),

            Self::ClosedSubtractionBound(_) => text(
                "طرح من حد عددي مخزن",
                "يبقى الحد الأعلى أو الأدنى المخزن كافيًا بعد طرح الثابت المغلق",
            ),
            Self::ComplexModulusNonnegative => text(
                "مقياس مركب غير سالب",
                "المقياس المركب الرئيسي غير سالب",
            ),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_ar(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ar(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ar(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ar(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ar(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_ar(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_ar(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_ar(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_ar(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_ar(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_ar(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_ar(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_ar(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_ar(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_ar(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_ar(),
            Self::SubNonnegative(p) => p.rule_name_and_message_ar(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_ar(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_ar(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_ar(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_ar(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_ar(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_ar(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_ar(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_ar(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_ar(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_ar(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_ar(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_ar(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_ar(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_ar(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_ar(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_ar(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_ar(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ar(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_ar(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_ar(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_ar(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_ar(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_ar(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_ar(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_ar(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_ar(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_ar(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_ar(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_ar(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_ar(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_ar(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_ar(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_ar(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_ar(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_ar(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_ar(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_ar(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_ar(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ar(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ja(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ja(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ja(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ja(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_ja(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_ja(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_ja(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_ja(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_ja(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_ja(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_ja(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_ja(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_ja(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_ja(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_ja(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_ja(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_ja(),

            Self::ClosedSubtractionBound(_) => text(
                "保存済みの数値の境界からの減算",
                "保存済みの上界または下界は閉じた定数を引いた後も十分です",
            ),
            Self::ComplexModulusNonnegative => text(
                "複素数の絶対値の非負性",
                "複素数の主絶対値は非負です",
            ),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_ja(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ja(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ja(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ja(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ja(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_ja(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_ja(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_ja(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_ja(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_ja(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_ja(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_ja(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_ja(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_ja(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_ja(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_ja(),
            Self::SubNonnegative(p) => p.rule_name_and_message_ja(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_ja(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_ja(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_ja(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_ja(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_ja(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_ja(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_ja(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_ja(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_ja(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_ja(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_ja(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_ja(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_ja(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_ja(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_ja(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_ja(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_ja(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ja(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_ja(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_ja(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_ja(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_ja(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_ja(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_ja(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_ja(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_ja(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_ja(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_ja(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_ja(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_ja(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_ja(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_ja(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_ja(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_ja(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_ja(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_ja(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_ja(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_ja(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ja(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ko(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ko(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ko(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_ko(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_ko(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_ko(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_ko(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_ko(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_ko(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_ko(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_ko(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_ko(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_ko(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_ko(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_ko(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_ko(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_ko(),

            Self::ClosedSubtractionBound(_) => text(
                "저장된 수치 경계에서 빼기",
                "저장된 상한 또는 하한은 닫힌 상수를 뺀 후에도 충분합니다",
            ),
            Self::ComplexModulusNonnegative => text(
                "복소수 절댓값의 비음성",
                "복소수의 주 절댓값은 음이 아닙니다",
            ),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_ko(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ko(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ko(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ko(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ko(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_ko(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_ko(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_ko(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_ko(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_ko(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_ko(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_ko(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_ko(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_ko(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_ko(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_ko(),
            Self::SubNonnegative(p) => p.rule_name_and_message_ko(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_ko(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_ko(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_ko(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_ko(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_ko(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_ko(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_ko(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_ko(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_ko(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_ko(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_ko(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_ko(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_ko(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_ko(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_ko(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_ko(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_ko(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ko(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_ko(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_ko(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_ko(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_ko(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_ko(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_ko(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_ko(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_ko(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_ko(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_ko(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_ko(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_ko(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_ko(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_ko(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_ko(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_ko(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_ko(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_ko(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_ko(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_ko(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ko(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_vi(),
            Self::MulRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_vi(),
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_vi(),
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(p) => p.rule_name_and_message_vi(),
            Self::FloorLowerBound(p) => p.rule_name_and_message_vi(),
            Self::CeilUpperBound(p) => p.rule_name_and_message_vi(),
            Self::ExpWeakMonotone(p) => p.rule_name_and_message_vi(),
            Self::LnWeakMonotone(p) => p.rule_name_and_message_vi(),
            Self::ExpWeakOrderReflection(p) => p.rule_name_and_message_vi(),
            Self::LnWeakOrderReflection(p) => p.rule_name_and_message_vi(),
            Self::FactorialMonotone(p) => p.rule_name_and_message_vi(),
            Self::FloorMonotone(p)=>p.rule_name_and_message_vi(),
            Self::CeilMonotone(p)=>p.rule_name_and_message_vi(),
            Self::ComplexTriangle(p)=>p.rule_name_and_message_vi(),
            Self::FiniteSetSumTriangle(p)=>p.rule_name_and_message_vi(),
            Self::ComplexReverseTriangle(p)=>p.rule_name_and_message_vi(),
            Self::LcmCommonMultipleBound(p)=>p.rule_name_and_message_vi(),

            Self::ClosedSubtractionBound(_) => text(
                "Trừ từ cận số đã lưu",
                "Cận trên hoặc dưới đã lưu vẫn đủ sau khi trừ hằng đóng",
            ),
            Self::ComplexModulusNonnegative => text(
                "Môđun phức không âm",
                "Môđun phức chính không âm",
            ),
            Self::FromKnownGreaterEqual(p) => p.rule_name_and_message_vi(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_vi(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_vi(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_vi(),
            Self::FromKnownLess(p) => p.rule_name_and_message_vi(),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_name_and_message_vi(),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_name_and_message_vi(),
            Self::ArccosPrincipalLowerBound(p) => p.rule_name_and_message_vi(),
            Self::ArccosPrincipalUpperBound(p) => p.rule_name_and_message_vi(),
            Self::UnitCircleLowerBound(p) => p.rule_name_and_message_vi(),
            Self::UnitCircleUpperBound(p) => p.rule_name_and_message_vi(),
            Self::AbsNonnegative(p) => p.rule_name_and_message_vi(),
            Self::AddRightNonnegative(p) => p.rule_name_and_message_vi(),
            Self::AddLeftNonnegative(p) => p.rule_name_and_message_vi(),
            Self::AddRightCongruence(p) => p.rule_name_and_message_vi(),
            Self::AddLeftCongruence(p) => p.rule_name_and_message_vi(),
            Self::SubNonnegative(p) => p.rule_name_and_message_vi(),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_name_and_message_vi(),
            Self::MulRightNonnegativeMonotone(p) => p.rule_name_and_message_vi(),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_name_and_message_vi(),
            Self::AbsLeImpliesUpper(p) => p.rule_name_and_message_vi(),
            Self::AbsLeImpliesNegUpper(p) => p.rule_name_and_message_vi(),
            Self::AbsSelfUpper(p) => p.rule_name_and_message_vi(),
            Self::AbsSelfLower(p) => p.rule_name_and_message_vi(),
            Self::AbsTriangleInequality(p) => p.rule_name_and_message_vi(),
            Self::AbsReverseTriangleAdd(p) => p.rule_name_and_message_vi(),
            Self::AbsReverseTriangleSub(p) => p.rule_name_and_message_vi(),
            Self::SumOfNonnegatives(p) => p.rule_name_and_message_vi(),
            Self::ProductOfNonnegatives(p) => p.rule_name_and_message_vi(),
            Self::EvenPowNonnegative(p) => p.rule_name_and_message_vi(),
            Self::PowNonnegFromPositiveBase(p) => p.rule_name_and_message_vi(),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_name_and_message_vi(),
            Self::SqrtNonnegative(p) => p.rule_name_and_message_vi(),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_name_and_message_vi(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_vi(),
            Self::LogOrderPreservingWeak(p) => p.rule_name_and_message_vi(),
            Self::LogWeakDecreasing(p) => p.rule_name_and_message_vi(),
            Self::LessEqualTransitivity(p) => p.rule_name_and_message_vi(),
            Self::LessEqualFromNonnegDifference(p) => p.rule_name_and_message_vi(),
            Self::LessEqualFromNonpositiveDifference(p) => p.rule_name_and_message_vi(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.rule_name_and_message_vi(),

            Self::NonnegDifferenceFromLessEqual(p) => p.rule_name_and_message_vi(),
            Self::ModRemainderNonnegative(p) => p.rule_name_and_message_vi(),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_name_and_message_vi(),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_name_and_message_vi(),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_name_and_message_vi(),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_name_and_message_vi(),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_name_and_message_vi(),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_name_and_message_vi(),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_name_and_message_vi(),
            Self::IntegerSuccessorLe(p) => p.rule_name_and_message_vi(),
            Self::IntegerAdjacencyLe(p) => p.rule_name_and_message_vi(),
            Self::IntegerPredecessorLe(p) => p.rule_name_and_message_vi(),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_name_and_message_vi(),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetMaxMemberLe(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetMinMemberLe(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_name_and_message_vi(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_vi(),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_name_and_message_vi(),
        }
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::MulLeftNonpositiveReversesWeakLessEqual(_) => None,
            Self::MulRightNonpositiveReversesWeakLessEqual(_) => None,
            Self::MulLeftRightNonpositiveReversesWeakLessEqual(_) => None,
            Self::MulRightLeftNonpositiveReversesWeakLessEqual(_) => None,
            Self::FloorLowerBound(_) => None,
            Self::CeilUpperBound(_) => None,
            Self::ClosedSubtractionBound(p) => Some(p.bound.cite_fact_id),
            Self::FromKnownGreaterEqual(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownLess(p) => p.premise_proof.cite_fact_id(),
            Self::AbsLeImpliesUpper(p) => p.premise_proof.cite_fact_id(),
            Self::AbsLeImpliesNegUpper(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownInPositiveNatural(p) => p.premise_proof.cite_fact_id(),
            Self::LessEqualTransitivity(_) => None,
            Self::LessEqualFromNonnegDifference(p) => p.premise_proof.cite_fact_id(),
            Self::LessEqualFromNonpositiveDifference(p) => p.premise_proof.cite_fact_id(),
            Self::NonpositiveDifferenceFromLessEqual(p) => p.premise_proof.cite_fact_id(),

            Self::NonnegDifferenceFromLessEqual(p) => p.premise_proof.cite_fact_id(),
            Self::NumericLowerBoundWeakenLe(p) => Some(p.cite_fact_id),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => Some(p.cite_fact_id),
            Self::NumericUpperBoundWeakenLe(p) => Some(p.cite_fact_id),
            Self::OrderFlipMulMinusOne(p) => p.premise_proof.cite_fact_id(),
            Self::OrderSignFromNegativeLiteralBound(p) => Some(p.cite_fact_id),
            _ => None,
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Closed numeric comparison",
            "Both sides are closed numbers and compare as stated",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "封闭数值比较",
            "两边都是可计算的数，并满足所述比较",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "封閉數值比較",
            "兩邊為封閉數值且符合所述比較",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Comparaison numérique fermée",
            "Les deux membres sont des nombres fermés et satisfont la comparaison indiquée",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сравнение замкнутых числовых выражений",
            "Обе части являются замкнутыми числами и удовлетворяют указанному сравнению",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Comparación numérica cerrada",
            "Ambos lados son números cerrados y cumplen la comparación indicada",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مقارنة عددية مغلقة",
            "الطرفان عددان مغلقان ويحققان المقارنة المذكورة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "閉じた数値式の比較",
            "両辺は閉じた数値であり、指定された比較を満たします",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "닫힌 수치 식 비교",
            "양변은 닫힌 수이며 명시된 비교를 만족합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "So sánh số đóng",
            "Hai vế là số đóng và thỏa so sánh đã nêu",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl OrderReflexivityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Order reflexivity",
            "A quantity is less-or-equal to itself",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "序的自反性",
            "任何量都不大于也不小于自己（≤ 自身）",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("序關係自反性", "任一量小於或等於自身")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Réflexivité de l'ordre",
            "Une quantité est inférieure ou égale à elle-même",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Рефлексивность порядка",
            "Величина меньше или равна самой себе",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Reflexividad del orden",
            "Una cantidad es menor o igual a sí misma",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انعكاسية الترتيب",
            "الكمية أصغر من نفسها أو تساويها",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("順序の反射性", "量は自身以下です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "순서 반사성",
            "양은 자기 자신보다 작거나 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính phản xạ của thứ tự",
            "Một đại lượng nhỏ hơn hoặc bằng chính nó",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FromKnownLessBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "From known less",
            "The weak order follows from a known strict less fact",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "已知严格小于",
            "弱序目标由已知的严格小于推出",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("由已知小於", "弱序由已知嚴格小於命題得出")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Depuis une inégalité inférieure connue",
            "L'ordre large découle d'une inégalité stricte inférieure connue",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Из известного меньшего значения",
            "Нестрогий порядок следует из известного строгого уменьшения",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desde desigualdad menor conocida",
            "El orden débil se deduce de desigualdad estricta menor conocida",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "من علاقة أصغر معلومة",
            "ينتج الترتيب غير الصارم من علاقة أصغر صارمة معلومة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の小なり関係から",
            "広義順序は既知の狭義の小なり命題から導かれます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 작음 관계에서",
            "약한 순서는 알려진 엄격한 작음 명제에서 도출됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Từ quan hệ nhỏ hơn đã biết",
            "Thứ tự không nghiêm ngặt suy ra từ quan hệ nhỏ hơn nghiêm ngặt đã biết",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ArcsinPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "arcsin lower bound",
            "arcsin stays within its principal lower bound",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arcsin 下界",
            "arcsin 落在其主值下界内",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arcsin 下界",
            "arcsin 不低於主值下界",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne inférieure de arcsin",
            "arcsin respecte sa borne principale inférieure",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нижняя граница arcsin",
            "arcsin не ниже своей главной нижней границы",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota inferior de arcsin",
            "arcsin respeta su cota principal inferior",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد أدنى لـ arcsin",
            "arcsin يبقى ضمن حده الرئيسي الأدنى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arcsin の下界",
            "arcsin は主値の下界以上です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arcsin 하한",
            "arcsin는 주값 하한 이상입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận dưới arcsin",
            "arcsin giữ trong cận dưới chính",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ArcsinPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "arcsin upper bound",
            "arcsin stays within its principal upper bound",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arcsin 上界",
            "arcsin 落在其主值上界内",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arcsin 上界",
            "arcsin 不高於主值上界",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne supérieure de arcsin",
            "arcsin respecte sa borne principale supérieure",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Верхняя граница arcsin",
            "arcsin не выше своей главной верхней границы",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota superior de arcsin",
            "arcsin respeta su cota principal superior",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد أعلى لـ arcsin",
            "arcsin يبقى ضمن حده الرئيسي الأعلى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arcsin の上界",
            "arcsin は主値の上界以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arcsin 상한",
            "arcsin는 주값 상한 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận trên arcsin",
            "arcsin giữ trong cận trên chính",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ArccosPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "arccos lower bound",
            "arccos stays within its principal lower bound",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arccos 下界",
            "arccos 落在其主值下界内",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arccos 下界",
            "arccos 不低於主值下界",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne inférieure de arccos",
            "arccos respecte sa borne principale inférieure",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нижняя граница arccos",
            "arccos не ниже своей главной нижней границы",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota inferior de arccos",
            "arccos respeta su cota principal inferior",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد أدنى لـ arccos",
            "arccos يبقى ضمن حده الرئيسي الأدنى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arccos の下界",
            "arccos は主値の下界以上です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arccos 하한",
            "arccos는 주값 하한 이상입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận dưới arccos",
            "arccos giữ trong cận dưới chính",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ArccosPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "arccos upper bound",
            "arccos stays within its principal upper bound",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "arccos 上界",
            "arccos 落在其主值上界内",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "arccos 上界",
            "arccos 不高於主值上界",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne supérieure de arccos",
            "arccos respecte sa borne principale supérieure",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Верхняя граница arccos",
            "arccos не выше своей главной верхней границы",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota superior de arccos",
            "arccos respeta su cota principal superior",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد أعلى لـ arccos",
            "arccos يبقى ضمن حده الرئيسي الأعلى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "arccos の上界",
            "arccos は主値の上界以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "arccos 상한",
            "arccos는 주값 상한 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận trên arccos",
            "arccos giữ trong cận trên chính",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl UnitCircleLowerBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Unit-circle lower bound",
            "Trig values on the unit circle respect the lower bound",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "单位圆下界",
            "单位圆上的三角函数值满足下界",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("單位圓下界", "單位圓三角值符合下界")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne inférieure du cercle unité",
            "Les valeurs trigonométriques sur le cercle unité respectent la borne inférieure",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нижняя граница единичной окружности",
            "Тригонометрические значения на единичной окружности соблюдают нижнюю границу",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota inferior del círculo unitario",
            "Los valores trigonométricos del círculo unitario respetan la cota inferior",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد أدنى لدائرة الوحدة",
            "القيم المثلثية على دائرة الوحدة تحقق الحد الأدنى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "単位円の下界",
            "単位円上の三角関数値は下界を満たします",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "단위원 하한",
            "단위원의 삼각함숫값은 하한을 만족합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận dưới đường tròn đơn vị",
            "Giá trị lượng giác trên đường tròn đơn vị thỏa cận dưới",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl UnitCircleUpperBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Unit-circle upper bound",
            "Trig values on the unit circle respect the upper bound",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "单位圆上界",
            "单位圆上的三角函数值满足上界",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("單位圓上界", "單位圓三角值符合上界")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne supérieure du cercle unité",
            "Les valeurs trigonométriques sur le cercle unité respectent la borne supérieure",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Верхняя граница единичной окружности",
            "Тригонометрические значения на единичной окружности соблюдают верхнюю границу",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota superior del círculo unitario",
            "Los valores trigonométricos del círculo unitario respetan la cota superior",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد أعلى لدائرة الوحدة",
            "القيم المثلثية على دائرة الوحدة تحقق الحد الأعلى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "単位円の上界",
            "単位円上の三角関数値は上界を満たします",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "단위원 상한",
            "단위원의 삼각함숫값은 상한을 만족합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận trên đường tròn đơn vị",
            "Giá trị lượng giác trên đường tròn đơn vị thỏa cận trên",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Nonnegativity of absolute value", "Absolute value is nonnegative")
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("绝对值非负", "绝对值非负")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("絕對值非負", "絕對值非負")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Valeur absolue positive ou nulle",
            "La valeur absolue est non négative",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text("Неотрицательность модуля", "Модуль неотрицателен")
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "No negatividad del valor absoluto",
            "El valor absoluto es no negativo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("عدم سلبية القيمة المطلقة", "القيمة المطلقة غير سالبة")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("絶対値の非負性", "絶対値は非負です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("절댓값의 비음수성", "절댓값은 음이 아닙니다")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Giá trị tuyệt đối không âm", "Giá trị tuyệt đối không âm")
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AddRightNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Add right nonnegative",
            "Adding a nonnegative term on the right preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("右边加非负", "右边加上非负项保持 ≤")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("右加非負項", "右加非負項保持 ≤")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Addition non négative à droite",
            "Ajouter un terme non négatif à droite préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неотрицательное сложение справа",
            "Добавление неотрицательного члена справа сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma no negativa derecha",
            "Sumar un término no negativo a la derecha conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "جمع غير سالب أيمن",
            "إضافة حد غير سالب يمينًا تحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "右に非負の項を加算",
            "右に非負の項を加えると ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "오른쪽 비음수 덧셈",
            "오른쪽에 음이 아닌 항을 더하면 ≤가 보존됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cộng không âm bên phải",
            "Cộng hạng không âm bên phải bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AddLeftNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Add left nonnegative",
            "Adding a nonnegative term on the left preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("左边加非负", "左边加上非负项保持 ≤")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("左加非負項", "左加非負項保持 ≤")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Addition non négative à gauche",
            "Ajouter un terme non négatif à gauche préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неотрицательное сложение слева",
            "Добавление неотрицательного члена слева сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma no negativa izquierda",
            "Sumar un término no negativo a la izquierda conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "جمع غير سالب أيسر",
            "إضافة حد غير سالب يسارًا تحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "左に非負の項を加算",
            "左に非負の項を加えると ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "왼쪽 비음수 덧셈",
            "왼쪽에 음이 아닌 항을 더하면 ≤가 보존됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cộng không âm bên trái",
            "Cộng hạng không âm bên trái bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AddRightCongruenceBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Add right (≤)",
            "Adding the same term on the right preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("右边加（≤）", "右边加上相同项保持 ≤")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("右加法（≤）", "右加相同項保持 ≤")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Addition à droite (≤)",
            "Ajouter le même terme à droite préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сложение справа (≤)",
            "Добавление одного члена справа сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma derecha (≤)",
            "Sumar el mismo término a la derecha conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "جمع أيمن (≤)",
            "إضافة الحد نفسه يمينًا تحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "右加算（≤）",
            "右に同じ項を加えても ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "오른쪽 덧셈 (≤)",
            "오른쪽에 같은 항을 더하면 ≤가 보존됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cộng phải (≤)",
            "Cộng cùng hạng bên phải bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AddLeftCongruenceBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Add left (≤)",
            "Adding the same term on the left preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("左边加（≤）", "左边加上相同项保持 ≤")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("左加法（≤）", "左加相同項保持 ≤")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Addition à gauche (≤)",
            "Ajouter le même terme à gauche préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сложение слева (≤)",
            "Добавление одного члена слева сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma izquierda (≤)",
            "Sumar el mismo término a la izquierda conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "جمع أيسر (≤)",
            "إضافة الحد نفسه يسارًا تحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "左加算（≤）",
            "左に同じ項を加えても ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "왼쪽 덧셈 (≤)",
            "왼쪽에 같은 항을 더하면 ≤가 보존됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cộng trái (≤)",
            "Cộng cùng hạng bên trái bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl SubNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonnegative difference from a weak order",
            "A difference is nonnegative under the stated premises",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("由非严格大小关系得到差非负", "在所述前提下差非负")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("由非嚴格大小關係得到差非負", "所述前提下差非負")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Différence positive ou nulle issue d’un ordre large",
            "Une différence est non négative sous les prémisses indiquées",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неотрицательность разности из нестрогого порядка",
            "Разность неотрицательна при указанных предпосылках",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Diferencia no negativa a partir del orden no estricto",
            "Una diferencia es no negativa bajo las premisas indicadas",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فرق غير سالب من ترتيب غير صارم",
            "الفرق غير سالب تحت المقدمات المذكورة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "弱い大小関係から得られる非負の差",
            "指定された前提のもとで差は非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "비엄격 순서에서 얻는 음이 아닌 차",
            "명시된 전제에서 차는 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hiệu không âm từ thứ tự không nghiêm ngặt",
            "Hiệu không âm dưới các tiền đề đã nêu",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl MulLeftNonnegativeMonotoneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "× left monotone (≤)",
            "Multiplying on the left by a nonnegative factor preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "左乘单调（≤）",
            "左边乘以非负因子保持 ≤",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "左乘單調性（≤）",
            "左乘非負因子保持 ≤",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie de multiplication gauche (≤)",
            "Multiplier à gauche par un facteur non négatif préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Монотонность умножения слева (≤)",
            "Умножение слева на неотрицательный множитель сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía de multiplicación izquierda (≤)",
            "Multiplicar a la izquierda por factor no negativo conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة الضرب الأيسر (≤)",
            "الضرب يسارًا بعامل غير سالب يحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "左乗算の単調性（≤）",
            "左に非負因子を掛けると ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "왼쪽 곱셈 단조성 (≤)",
            "왼쪽에 음이 아닌 인자를 곱하면 ≤가 보존됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đơn điệu nhân trái (≤)",
            "Nhân bên trái với thừa số không âm bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl MulRightNonnegativeMonotoneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "× right monotone (≤)",
            "Multiplying on the right by a nonnegative factor preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "右乘单调（≤）",
            "右边乘以非负因子保持 ≤",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "右乘單調性（≤）",
            "右乘非負因子保持 ≤",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie de multiplication droite (≤)",
            "Multiplier à droite par un facteur non négatif préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Монотонность умножения справа (≤)",
            "Умножение справа на неотрицательный множитель сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía de multiplicación derecha (≤)",
            "Multiplicar a la derecha por factor no negativo conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة الضرب الأيمن (≤)",
            "الضرب يمينًا بعامل غير سالب يحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "右乗算の単調性（≤）",
            "右に非負因子を掛けると ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "오른쪽 곱셈 단조성 (≤)",
            "오른쪽에 음이 아닌 인자를 곱하면 ≤가 보존됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đơn điệu nhân phải (≤)",
            "Nhân bên phải với thừa số không âm bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsLeFromSymmetricBoundsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "|x| ≤ M from ± bounds",
            "Absolute value is bounded by M when -M ≤ x ≤ M",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由 ± 界得 |x| ≤ M",
            "当 -M ≤ x ≤ M 时，|x| ≤ M",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由正負界得 |x| ≤ M",
            "當 -M ≤ x ≤ M，絕對值不大於 M",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "|x| ≤ M depuis les bornes ±",
            "La valeur absolue est bornée par M si -M ≤ x ≤ M",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "|x| ≤ M из границ ±",
            "Модуль ограничен M при -M ≤ x ≤ M",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "|x| ≤ M desde cotas ±",
            "El valor absoluto está acotado por M si -M ≤ x ≤ M",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "|x| ≤ M من حدود ±",
            "القيمة المطلقة محدودة بـ M عندما -M ≤ x ≤ M",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "± の境界から |x| ≤ M",
            "-M ≤ x ≤ M の場合、絶対値は M 以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "± 경계로 |x| ≤ M",
            "-M ≤ x ≤ M이면 절댓값은 M 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "|x| ≤ M từ cận ±",
            "Giá trị tuyệt đối bị chặn bởi M khi -M ≤ x ≤ M",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsLeImpliesUpperBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Upper bound from absolute value",
            "An absolute-value upper bound implies the same bound on x",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由绝对值上界得到原数上界",
            "绝对值上界蕴含 x 的同样上界",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由絕對值上界得到原數上界",
            "絕對值上界同樣限制 x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne supérieure issue de la valeur absolue",
            "Une borne supérieure de valeur absolue borne aussi x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Верхняя граница из оценки модуля",
            "Верхняя граница модуля также ограничивает x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota superior a partir del valor absoluto",
            "Una cota superior de valor absoluto también acota x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد علوي من القيمة المطلقة",
            "الحد الأعلى للقيمة المطلقة يحد x أيضًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "絶対値の上界からの上界",
            "絶対値の上界は x にも同じ上界を与えます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "절댓값 상계로부터 얻는 상계",
            "절댓값 상한은 x에도 같은 상한을 줍니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận trên từ giá trị tuyệt đối",
            "Cận trên giá trị tuyệt đối cũng chặn x",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsLeImpliesNegUpperBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Upper bound on the opposite from absolute value",
            "An absolute-value upper bound implies the same bound on -x",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由绝对值上界得到相反数上界",
            "绝对值上界蕴含 -x 的同样上界",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由絕對值上界得到相反數上界",
            "絕對值上界同樣限制 -x",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne de l’opposé issue de la valeur absolue",
            "Une borne supérieure de valeur absolue borne aussi -x",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Верхняя граница противоположного числа из оценки модуля",
            "Верхняя граница модуля также ограничивает -x",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota del opuesto a partir del valor absoluto",
            "Una cota superior de valor absoluto también acota -x",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد علوي للمعاكس من القيمة المطلقة",
            "الحد الأعلى للقيمة المطلقة يحد -x أيضًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "絶対値の上界から得る符号反転値の上界",
            "絶対値の上界は -x にも同じ上界を与えます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "절댓값 상계로부터 얻는 반대 수의 상계",
            "절댓값 상한은 -x에도 같은 상한을 줍니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận trên của số đối từ giá trị tuyệt đối",
            "Cận trên giá trị tuyệt đối cũng chặn -x",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsSelfUpperBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Absolute value bounds the real number above",
            "A quantity is at most its absolute value",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数不大于自身的绝对值", "任何量都不大于其绝对值")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("實數不大於自身的絕對值", "任一量至多為其絕對值")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Valeur absolue comme majorant du réel",
            "Une quantité est au plus sa valeur absolue",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Модуль как верхняя граница вещественного числа",
            "Величина не больше своего модуля",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Valor absoluto como cota superior del real",
            "Una cantidad es como máximo su valor absoluto",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة المطلقة حد علوي للعدد الحقيقي",
            "الكمية لا تزيد على قيمتها المطلقة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("実数の絶対値による上界", "量はその絶対値以下です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("실수의 절댓값 상계", "양은 자기 절댓값 이하입니다")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị tuyệt đối là cận trên của số thực",
            "Một đại lượng không vượt quá giá trị tuyệt đối của nó",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsSelfLowerBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Negative absolute value bounds the real number below",
            "A quantity is at least the negation of its absolute value",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("实数不小于绝对值的相反数", "任何量都不小于其绝对值的相反数")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("實數不小於絕對值的相反數", "任一量至少為其絕對值的相反數")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Opposé de la valeur absolue comme minorant",
            "Une quantité est au moins l'opposé de sa valeur absolue",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Отрицательный модуль как нижняя граница",
            "Величина не меньше отрицания своего модуля",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Valor absoluto negativo como cota inferior",
            "Una cantidad es al menos el negativo de su valor absoluto",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "سالب القيمة المطلقة حد سفلي",
            "الكمية لا تقل عن سالب قيمتها المطلقة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("負の絶対値による下界", "量はその絶対値の負値以上です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "음의 절댓값 하계",
            "양은 자기 절댓값의 음수 이상입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Âm giá trị tuyệt đối là cận dưới",
            "Một đại lượng ít nhất bằng số đối của giá trị tuyệt đối của nó",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsTriangleInequalityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Triangle inequality for absolute value",
            "The Triangle inequality for absolute value rule gives: abs(a+b) ≤ abs(a)+abs(b)",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("绝对值的三角不等式", "绝对值的三角不等式可写为: abs(a+b) ≤ abs(a)+abs(b)")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("絕對值的三角不等式", "絕對值的三角不等式可寫為: abs(a+b) ≤ abs(a)+abs(b)")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inégalité triangulaire de la valeur absolue",
            "La propriété « Inégalité triangulaire de la valeur absolue » donne: abs(a+b) ≤ abs(a)+abs(b)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неравенство треугольника для модуля",
            "Свойство «Неравенство треугольника для модуля» выражается формулой: abs(a+b) ≤ abs(a)+abs(b)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desigualdad triangular del valor absoluto",
            "La propiedad «Desigualdad triangular del valor absoluto» se expresa como: abs(a+b) ≤ abs(a)+abs(b)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("متباينة المثلث للقيمة المطلقة", "تُكتب خاصية «متباينة المثلث للقيمة المطلقة» كما يلي: abs(a+b) ≤ abs(a)+abs(b)")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("絶対値の三角不等式", "絶対値の三角不等式は次の式で表されます: abs(a+b) ≤ abs(a)+abs(b)")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("절댓값의 삼각부등식", "절댓값의 삼각부등식은 다음 식으로 나타납니다: abs(a+b) ≤ abs(a)+abs(b)")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bất đẳng thức tam giác của giá trị tuyệt đối",
            "Tính chất «Bất đẳng thức tam giác của giá trị tuyệt đối» được biểu diễn bởi: abs(a+b) ≤ abs(a)+abs(b)",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsReverseTriangleAddBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Reverse triangle (|a|+|b|)",
            "Reverse triangle inequality for absolute values of a sum",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "反向三角（|a|+|b|）",
            "和的绝对值的反向三角不等式",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "反三角不等式（|a|+|b|）",
            "和的絕對值反三角不等式",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Triangle inverse (|a|+|b|)",
            "Inégalité triangulaire inverse pour la valeur absolue d'une somme",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратный треугольник (|a|+|b|)",
            "Обратное неравенство треугольника для модуля суммы",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Triángulo inverso (|a|+|b|)",
            "Desigualdad triangular inversa para valor absoluto de suma",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مثلث عكسي (|a|+|b|)",
            "متباينة المثلث العكسية للقيمة المطلقة للمجموع",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "逆三角不等式（|a|+|b|）",
            "和の絶対値の逆三角不等式",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "역삼각부등식 (|a|+|b|)",
            "합의 절댓값 역삼각부등식",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tam giác đảo (|a|+|b|)",
            "Bất đẳng thức tam giác đảo cho giá trị tuyệt đối của tổng",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl AbsReverseTriangleSubBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Reverse triangle (|a|-|b|)",
            "Reverse triangle inequality for absolute values of a difference",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "反向三角（|a|-|b|）",
            "差的绝对值的反向三角不等式",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "反三角不等式（|a|-|b|）",
            "差的絕對值反三角不等式",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Triangle inverse (|a|-|b|)",
            "Inégalité triangulaire inverse pour la valeur absolue d'une différence",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обратный треугольник (|a|-|b|)",
            "Обратное неравенство треугольника для модуля разности",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Triángulo inverso (|a|-|b|)",
            "Desigualdad triangular inversa para valor absoluto de diferencia",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مثلث عكسي (|a|-|b|)",
            "متباينة المثلث العكسية للقيمة المطلقة للفرق",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "逆三角不等式（|a|-|b|）",
            "差の絶対値の逆三角不等式",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "역삼각부등식 (|a|-|b|)",
            "차의 절댓값 역삼각부등식",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tam giác đảo (|a|-|b|)",
            "Bất đẳng thức tam giác đảo cho giá trị tuyệt đối của hiệu",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl SumOfNonnegativesBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Sum of nonnegatives ≥ 0",
            "A sum of nonnegative terms is nonnegative",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非负和 ≥ 0", "非负项之和非负")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("非負數和 ≥ 0", "非負項的和非負")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Somme de non-négatifs ≥ 0",
            "Une somme de termes non négatifs est non négative",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сумма неотрицательных ≥ 0",
            "Сумма неотрицательных членов неотрицательна",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Suma de no negativos ≥ 0",
            "Una suma de términos no negativos es no negativa",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموع غير السوالب ≥ 0",
            "مجموع حدود غير سالبة غير سالب",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非負数の和 ≥ 0",
            "非負の項の和は非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "비음수의 합 ≥ 0",
            "음이 아닌 항의 합은 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tổng số không âm ≥ 0",
            "Tổng các hạng không âm không âm",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ProductOfNonnegativesBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Product of nonnegatives ≥ 0",
            "A product of nonnegative factors is nonnegative",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("非负积 ≥ 0", "非负因子之积非负")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非負數乘積 ≥ 0",
            "非負因子的乘積非負",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Produit de non-négatifs ≥ 0",
            "Un produit de facteurs non négatifs est non négatif",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Произведение неотрицательных ≥ 0",
            "Произведение неотрицательных множителей неотрицательно",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Producto de no negativos ≥ 0",
            "Un producto de factores no negativos es no negativo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حاصل ضرب غير السوالب ≥ 0",
            "حاصل ضرب عوامل غير سالبة غير سالب",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非負数の積 ≥ 0",
            "非負因子の積は非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "비음수의 곱 ≥ 0",
            "음이 아닌 인자의 곱은 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tích số không âm ≥ 0",
            "Tích các thừa số không âm không âm",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl EvenPowNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Even power ≥ 0",
            "An even power of a checked real base is nonnegative",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "偶次幂 ≥ 0",
            "已验证的实数底数的偶次幂非负",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "偶數次方 ≥ 0",
            "經驗證實數底數的偶數次方非負",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Puissance paire ≥ 0",
            "Une puissance paire d'une base réelle vérifiée est non négative",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Чётная степень ≥ 0",
            "Чётная степень проверенного вещественного основания неотрицательна",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Potencia par ≥ 0",
            "Una potencia par de base real comprobada es no negativa",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قوة زوجية ≥ 0",
            "القوة الزوجية لأساس حقيقي متحقق منه غير سالبة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "偶数乗 ≥ 0",
            "検証済みの実数の底の偶数乗は非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "짝수 거듭제곱 ≥ 0",
            "검증된 실수 밑의 짝수 거듭제곱은 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lũy thừa chẵn ≥ 0",
            "Lũy thừa chẵn của cơ số thực đã kiểm tra không âm",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PowNonnegFromPositiveBaseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "pow ≥ 0 (pos base)",
            "A positive base raised to a real power is nonnegative where defined",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "幂 ≥ 0（正底）",
            "正底数的实数次幂在有定义时非负",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "正底數的冪 ≥ 0",
            "正底數的實數次方在定義成立時非負",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Puissance ≥ 0 (base positive)",
            "Une base positive à une puissance réelle est non négative là où elle est définie",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Степень ≥ 0 (положительное основание)",
            "Положительное основание в вещественной степени неотрицательно там, где определено",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Potencia ≥ 0 (base positiva)",
            "Una base positiva elevada a potencia real es no negativa donde está definida",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قوة ≥ 0 (أساس موجب)",
            "الأساس الموجب مرفوعًا لقوة حقيقية غير سالب حيث يكون معرّفًا",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "冪 ≥ 0（正の底）",
            "正の底の実数乗は定義されるところで非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "거듭제곱 ≥ 0(양수 밑)",
            "양의 밑의 실수 거듭제곱은 정의되는 곳에서 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lũy thừa ≥ 0 (cơ số dương)",
            "Cơ số dương nâng lũy thừa thực không âm khi xác định",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "pow ≥ 0 (nonneg base)",
            "A nonnegative base to a positive integer power is nonnegative",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "幂 ≥ 0（非负底）",
            "非负底数的正整数次幂非负",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非負底數的冪 ≥ 0",
            "非負底數的正整數次方非負",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Puissance ≥ 0 (base non négative)",
            "Une base non négative à une puissance entière positive est non négative",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Степень ≥ 0 (неотрицательное основание)",
            "Неотрицательное основание в положительной целой степени неотрицательно",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Potencia ≥ 0 (base no negativa)",
            "Una base no negativa elevada a potencia entera positiva es no negativa",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "قوة ≥ 0 (أساس غير سالب)",
            "الأساس غير السالب مرفوعًا لقوة صحيحة موجبة غير سالب",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "冪 ≥ 0（非負の底）",
            "非負の底の正の整数乗は非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "거듭제곱 ≥ 0(비음수 밑)",
            "음이 아닌 밑의 양의 정수 거듭제곱은 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lũy thừa ≥ 0 (cơ số không âm)",
            "Cơ số không âm nâng lũy thừa nguyên dương không âm",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl SqrtNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text("Nonnegativity of the principal square root", "Square root is nonnegative")
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("算术平方根非负", "平方根非负")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("算術平方根非負", "平方根非負")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Racine carrée principale positive ou nulle",
            "La racine carrée est non négative",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неотрицательность главного квадратного корня",
            "Квадратный корень неотрицателен",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "No negatividad de la raíz cuadrada principal",
            "La raíz cuadrada es no negativa",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("عدم سلبية الجذر التربيعي الرئيسي", "الجذر التربيعي غير سالب")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("主平方根の非負性", "平方根は非負です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("주제곱근의 비음수성", "제곱근은 음이 아닙니다")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Căn bậc hai chính không âm", "Căn bậc hai không âm")
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl SqrtMonotoneNondecreasingBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "√ monotone weak",
            "Square root is nondecreasing on [0,∞)",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "√ 弱单调",
            "平方根在 [0,∞) 上非减",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "平方根弱單調性",
            "平方根在 [0,∞) 上非遞減",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie large de √",
            "La racine carrée est croissante au sens large sur [0,∞)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нестрогая монотонность √",
            "Квадратный корень не убывает на [0,∞)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía débil de √",
            "La raíz cuadrada es no decreciente en [0,∞)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة غير صارمة لـ √",
            "الجذر التربيعي غير متناقص على [0,∞)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "√ の広義単調性",
            "平方根は [0,∞) 上で非減少です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "√ 약한 단조성",
            "제곱근은 [0,∞)에서 감소하지 않습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đơn điệu không nghiêm ngặt của √",
            "Căn bậc hai không giảm trên [0,∞)",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FromKnownInPositiveNaturalBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "From known in positive N",
            "The goal follows from a known positive-natural membership",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "已知属于正自然数",
            "目标由已知的正自然数成员关系推出",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由已知正自然數成員",
            "目標由已知正自然數成員關係得出",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Depuis une appartenance connue aux naturels positifs",
            "L'objectif découle d'une appartenance connue aux naturels positifs",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Из известной принадлежности положительным натуральным",
            "Цель следует из известной принадлежности положительным натуральным",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desde pertenencia conocida a naturales positivos",
            "El objetivo se deduce de pertenencia conocida a naturales positivos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "من انتماء معلوم للأعداد الطبيعية الموجبة",
            "ينتج الهدف من انتماء معلوم للأعداد الطبيعية الموجبة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の正の自然数への所属から",
            "目標は既知の正の自然数への所属から導かれます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 양의 자연수 소속에서",
            "목표는 알려진 양의 자연수 소속에서 도출됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Từ sự thuộc về số tự nhiên dương đã biết",
            "Mục tiêu suy ra từ sự thuộc về số tự nhiên dương đã biết",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl LogOrderPreservingWeakBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "log order weak",
            "Log with base > 1 preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "对数弱保序",
            "底大于 1 的对数保持 ≤",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "對數弱序",
            "底數 > 1 的對數保持 ≤",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ordre large du logarithme",
            "Le logarithme de base > 1 préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нестрогий порядок логарифма",
            "Логарифм с основанием > 1 сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Orden débil del logaritmo",
            "El logaritmo de base > 1 conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ترتيب غير صارم للوغاريتم",
            "اللوغاريتم بأساس > 1 يحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "対数の広義順序",
            "底 > 1 の対数は ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "로그의 약한 순서",
            "밑 > 1인 로그는 ≤를 보존합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thứ tự không nghiêm ngặt của logarit",
            "Logarit cơ số > 1 bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl LessEqualTransitivityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "≤ transitivity",
            "Less-or-equal is transitive",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("≤ 传递性", "≤ 具有传递性")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("≤ 遞移性", "小於或等於具遞移性")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Transitivité de ≤",
            "La relation inférieure ou égale est transitive",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Транзитивность ≤",
            "Отношение меньше или равно транзитивно",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Transitividad de ≤",
            "Menor o igual es transitivo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تعدي ≤",
            "علاقة أصغر أو يساوي متعدية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "≤ の推移性",
            "以下の関係は推移的です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "≤ 추이성",
            "작거나 같음은 추이적입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính bắc cầu của ≤",
            "Quan hệ nhỏ hơn hoặc bằng có tính bắc cầu",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl LessEqualFromNonnegDifferenceBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonnegative difference implies weak order",
            "The Nonnegative difference implies weak order law gives: 0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "差非负推出非严格大小关系",
            "差非负推出非严格大小关系可写为：0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "差非負推出非嚴格大小關係",
            "差非負推出非嚴格大小關係可寫為：0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Différence positive ou nulle et ordre large",
            "La propriété « Différence positive ou nulle et ordre large » donne: 0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неотрицательная разность даёт нестрогий порядок",
            "Свойство «Неотрицательная разность даёт нестрогий порядок» выражается равенством: 0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Diferencia no negativa implica orden no estricto",
            "La propiedad «Diferencia no negativa implica orden no estricto» se expresa como: 0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الفرق غير السالب يستلزم ترتيبًا غير صارم",
            "تُكتب خاصية «الفرق غير السالب يستلزم ترتيبًا غير صارم» كما يلي: 0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非負の差から得られる弱い大小関係",
            "非負の差から得られる弱い大小関係は次の式で表されます：0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "음이 아닌 차에서 얻는 비엄격 순서",
            "음이 아닌 차에서 얻는 비엄격 순서은 다음 식으로 나타납니다: 0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hiệu không âm suy ra thứ tự không nghiêm ngặt",
            "Tính chất «Hiệu không âm suy ra thứ tự không nghiêm ngặt» được biểu diễn bởi: 0 ≤ b-a ⇒ a ≤ b",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NonnegDifferenceFromLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Weak order gives a nonnegative difference",
            "Nonnegative difference follows from ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非严格大小关系推出差非负",
            "由 ≤ 得到非负差",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非嚴格大小關係推出差非負",
            "≤ 推出差非負",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ordre large et différence positive ou nulle",
            "Une différence non négative découle de ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нестрогий порядок даёт неотрицательную разность",
            "Неотрицательная разность следует из ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Orden no estricto da una diferencia no negativa",
            "Una diferencia no negativa se deduce de ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الترتيب غير الصارم يعطي فرقًا غير سالب",
            "ينتج الفرق غير السالب من ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "弱い大小関係による差の非負性",
            "≤ から差の非負性を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "비엄격 순서에 따른 차의 비음수성",
            "≤로 차의 비음성을 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thứ tự không nghiêm ngặt cho hiệu không âm",
            "Hiệu không âm suy ra từ ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl ModRemainderNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "mod remainder ≥ 0",
            "Euclidean remainder is nonnegative",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("模余数 ≥ 0", "欧几里得余数非负")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("模餘數 ≥ 0", "Euclid 餘數非負")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Reste modulaire ≥ 0",
            "Le reste euclidien est non négatif",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Остаток по модулю ≥ 0",
            "Евклидов остаток неотрицателен",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Resto modular ≥ 0",
            "El resto euclídeo es no negativo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "باقي القسمة ≥ 0",
            "الباقي الإقليدي غير سالب",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "剰余 ≥ 0",
            "ユークリッドの剰余は非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "나머지 ≥ 0",
            "유클리드 나머지는 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số dư ≥ 0",
            "Số dư Euclid không âm",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl DivMonotoneWeakSamePosDivisorBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "÷ monotone weak (pos)",
            "Division by the same positive divisor preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "除法弱单调（正）",
            "同除以正除数保持 ≤",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "正除數弱序單調性",
            "同除正數保持 ≤",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie large avec diviseur positif",
            "Diviser par le même diviseur positif préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нестрогая монотонность с положительным делителем",
            "Деление на один положительный делитель сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía débil con divisor positivo",
            "Dividir por el mismo divisor positivo conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة غير صارمة بمقسوم عليه موجب",
            "القسمة على المقسوم عليه الموجب نفسه تحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の除数の広義単調性",
            "同じ正の数で割ると ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양수 제수의 약한 단조성",
            "같은 양수로 나누면 ≤가 보존됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đơn điệu không nghiêm ngặt với số chia dương",
            "Chia cùng số chia dương bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetSizeNonnegativeLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonnegative cardinality of a finite set",
            "Finite-set size is nonnegative (as ≤)",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集合的基数非负",
            "有限集大小非负（写成 ≤）",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合的基數非負",
            "有限集合大小非負（以 ≤ 表示）",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Cardinal positif ou nul d’un ensemble fini",
            "La taille d'un ensemble fini est non négative (avec ≤)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неотрицательность мощности конечного множества",
            "Размер конечного множества неотрицателен (через ≤)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cardinalidad no negativa de un conjunto finito",
            "El tamaño del conjunto finito es no negativo (con ≤)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدد عناصر المجموعة المنتهية غير سالب",
            "حجم المجموعة المنتهية غير سالب (بصيغة ≤)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の要素数の非負性",
            "有限集合の大きさは非負です（≤ 形式）",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한집합 원소 수의 비음수성",
            "유한 집합의 크기는 음이 아닙니다(≤ 형식)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lực lượng của tập hữu hạn không âm",
            "Kích thước tập hữu hạn không âm (dạng ≤)",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetSizeAtLeastOneLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonempty finite set has at least one element",
            "A nonempty finite set has size at least one (as ≤)",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非空有限集合至少有一个元素",
            "非空有限集大小至少为 1（写成 ≤）",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非空有限集合至少有一個元素",
            "非空有限集合的大小至少為一（以 ≤ 表示）",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ensemble fini non vide ayant au moins un élément",
            "Un ensemble fini non vide a au moins un élément (avec ≤)",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Непустое конечное множество содержит хотя бы один элемент",
            "Непустое конечное множество имеет размер не меньше одного (через ≤)",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conjunto finito no vacío con al menos un elemento",
            "Un conjunto finito no vacío tiene tamaño al menos uno (con ≤)",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "المجموعة المنتهية غير الخالية لها عنصر واحد على الأقل",
            "المجموعة المنتهية غير الخالية لها عنصر واحد على الأقل (بصيغة ≤)",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非空の有限集合には少なくとも一つの要素がある",
            "空でない有限集合の大きさは少なくとも一です（≤ 形式）",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "비어 있지 않은 유한집합에는 적어도 한 원소가 있음",
            "비어 있지 않은 유한 집합의 크기는 적어도 1입니다(≤ 형식)",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập hữu hạn khác rỗng có ít nhất một phần tử",
            "Tập hữu hạn không rỗng có kích thước ít nhất một (dạng ≤)",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetSizeSubsetLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cardinality is monotone under finite-set inclusion",
            "Subset relation implies a weak inequality on finite-set sizes",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "有限集合包含关系保持基数顺序",
            "子集关系蕴含有限集大小的弱不等式",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "有限集合包含關係保持基數順序",
            "子集關係推出有限集合大小的弱不等式",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie du cardinal par inclusion finie",
            "L'inclusion implique une inégalité large sur les tailles finies",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Монотонность мощности при включении конечных множеств",
            "Включение даёт нестрогое неравенство размеров конечных множеств",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía de la cardinalidad por inclusión finita",
            "La inclusión implica desigualdad débil de tamaños finitos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة عدد العناصر تحت احتواء المجموعات المنتهية",
            "الاحتواء الجزئي يستلزم متباينة غير صارمة لأحجام المجموعات المنتهية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の包含関係に対する要素数の単調性",
            "包含関係から有限集合の大きさの広義不等式を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한집합 포함에 대한 원소 수의 단조성",
            "부분집합 관계로 유한 집합 크기의 약한 부등식을 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính đơn điệu của lực lượng theo bao hàm hữu hạn",
            "Quan hệ tập con suy ra bất đẳng thức không nghiêm ngặt về kích thước hữu hạn",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl DivMonotoneWeakSameNegDivisorBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "÷ monotone weak (neg)",
            "Division by the same negative divisor reverses and preserves ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "除法弱单调（负）",
            "同除以负除数反转并保持 ≤",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "負除數弱序單調性",
            "同除負數反轉並保持 ≤",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie large avec diviseur négatif",
            "Diviser par le même diviseur négatif inverse et préserve ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нестрогая монотонность с отрицательным делителем",
            "Деление на один отрицательный делитель обращает и сохраняет ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía débil con divisor negativo",
            "Dividir por el mismo divisor negativo invierte y conserva ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة غير صارمة بمقسوم عليه سالب",
            "القسمة على المقسوم عليه السالب نفسه تعكس وتحفظ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "負の除数の広義単調性",
            "同じ負の数で割ると順序を反転して ≤ を保ちます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "음수 제수의 약한 단조성",
            "같은 음수로 나누면 순서를 반전하고 ≤를 보존합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đơn điệu không nghiêm ngặt với số chia âm",
            "Chia cùng số chia âm đảo chiều và bảo toàn ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl LessEqualFromPosDivProductBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "≤ from positive divisor product",
            "A product bound with positive divisor yields ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由正除数积得 ≤",
            "正除数的积界给出 ≤",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由正除數乘積得 ≤",
            "正除數的乘積界得 ≤",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "≤ depuis produit à diviseur positif",
            "Une borne de produit avec diviseur positif donne ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "≤ из произведения с положительным делителем",
            "Граница произведения с положительным делителем даёт ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "≤ desde producto con divisor positivo",
            "Una cota de producto con divisor positivo da ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "≤ من حاصل ضرب بمقسوم عليه موجب",
            "حد حاصل ضرب مع مقسوم عليه موجب يعطي ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の除数の積から ≤",
            "正の除数を伴う積の境界から ≤ を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양의 제수 곱으로 ≤",
            "양의 제수가 있는 곱의 경계로 ≤를 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "≤ từ tích với số chia dương",
            "Cận tích với số chia dương suy ra ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl LessEqualFromPosDenomQuotientBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "≤ from positive-denom quotient",
            "A quotient bound with positive denominator yields ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由正分母商得 ≤",
            "正分母的商界给出 ≤",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由正分母商得 ≤",
            "正分母的商界得 ≤",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "≤ depuis quotient à dénominateur positif",
            "Une borne de quotient à dénominateur positif donne ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "≤ из частного с положительным знаменателем",
            "Граница частного с положительным знаменателем даёт ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "≤ desde cociente con denominador positivo",
            "Una cota de cociente con denominador positivo da ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "≤ من خارج قسمة بمقام موجب",
            "حد خارج قسمة بمقام موجب يعطي ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の分母の商から ≤",
            "正の分母を伴う商の境界から ≤ を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양의 분모 몫으로 ≤",
            "양의 분모가 있는 몫의 경계로 ≤를 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "≤ từ thương có mẫu dương",
            "Cận thương với mẫu dương suy ra ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NumericLowerBoundWeakenLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Weaken numeric lower (≤)",
            "A numeric lower bound weakens under ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "放宽数值下界（≤）",
            "数值下界在 ≤ 下可放宽",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "放寬數值下界（≤）",
            "數值下界依 ≤ 放寬",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Relâchement de borne inférieure (≤)",
            "Une borne inférieure numérique se relâche sous ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Ослабление нижней границы (≤)",
            "Числовая нижняя граница ослабляется по ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Debilitar cota inferior (≤)",
            "Una cota inferior numérica se debilita bajo ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "إضعاف الحد الأدنى (≤)",
            "الحد الأدنى العددي يضعف تحت ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "数値下界の緩和（≤）",
            "数値の下界を ≤ で緩めます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "수치 하한 완화 (≤)",
            "수치 하한을 ≤로 완화합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Nới cận dưới (≤)",
            "Cận dưới số được nới theo ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Lower bound via predecessor",
            "A numeric lower bound follows from a strict predecessor comparison",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由前驱得下界",
            "由严格前驱比较得到数值下界",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由前驅得下界",
            "嚴格前驅比較得數值下界",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne inférieure via prédécesseur",
            "Une borne numérique inférieure découle d'une comparaison stricte du prédécesseur",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Нижняя граница через предыдущее значение",
            "Числовая нижняя граница следует из строгого сравнения предыдущего значения",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota inferior por predecesor",
            "Una cota inferior numérica se deduce de comparación estricta del predecesor",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد أدنى عبر السابق",
            "ينتج الحد الأدنى العددي من مقارنة صارمة للسابق",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "直前の値による下界",
            "直前の値の狭義比較から数値下界を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "이전 값으로 하한",
            "이전 값의 엄격한 비교로 수치 하한을 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận dưới qua giá trị liền trước",
            "Cận dưới số suy ra từ so sánh nghiêm ngặt với giá trị liền trước",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl NumericUpperBoundWeakenLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Weaken numeric upper (≤)",
            "A numeric upper bound weakens under ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "放宽数值上界（≤）",
            "数值上界在 ≤ 下可放宽",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "放寬數值上界（≤）",
            "數值上界依 ≤ 放寬",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Relâchement de borne supérieure (≤)",
            "Une borne supérieure numérique se relâche sous ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Ослабление верхней границы (≤)",
            "Числовая верхняя граница ослабляется по ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Debilitar cota superior (≤)",
            "Una cota superior numérica se debilita bajo ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "إضعاف الحد الأعلى (≤)",
            "الحد الأعلى العددي يضعف تحت ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "数値上界の緩和（≤）",
            "数値の上界を ≤ で緩めます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "수치 상한 완화 (≤)",
            "수치 상한을 ≤로 완화합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Nới cận trên (≤)",
            "Cận trên số được nới theo ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl IntegerSuccessorLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Integer bounded above by its successor",
            "An integer is ≤ its successor",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数不大于其后继", "整数 ≤ 其后继")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("整數不大於其後繼", "整數 ≤ 其後繼")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Entier majoré par son successeur",
            "Un entier est ≤ à son successeur",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Целое не больше своего следующего числа",
            "Целое число ≤ следующего значения",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Entero acotado por su sucesor",
            "Un entero es ≤ a su sucesor",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("العدد الصحيح لا يتجاوز تاليه", "العدد الصحيح ≤ تاليه")
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("整数と後続整数の弱い大小関係", "整数はその後続値以下です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "정수와 다음 정수의 비엄격 순서",
            "정수는 그 다음 값 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text("Số nguyên không lớn hơn số kế tiếp", "Số nguyên ≤ số liền sau")
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl IntegerAdjacencyLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Integer adjacency ≤",
            "Adjacent integers compare by ≤",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("整数相邻 ≤", "相邻整数按 ≤ 比较")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("相鄰整數 ≤", "相鄰整數符合 ≤")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Entiers adjacents ≤",
            "Les entiers adjacents se comparent par ≤",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Соседние целые ≤",
            "Соседние целые сравниваются по ≤",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Enteros adyacentes ≤",
            "Enteros adyacentes se comparan por ≤",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "أعداد صحيحة متجاورة ≤",
            "الأعداد الصحيحة المتجاورة تقارن بـ ≤",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "隣接整数 ≤",
            "隣接する整数は ≤ で比較されます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "인접 정수 ≤",
            "인접한 정수는 ≤로 비교됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số nguyên kề nhau ≤",
            "Các số nguyên kề nhau so sánh theo ≤",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl IntegerPredecessorLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Predecessor bounded above by the integer",
            "An integer predecessor is ≤ the integer",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("前驱不大于原整数", "整数前驱 ≤ 该整数")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("前驅不大於原整數", "整數前驅 ≤ 該整數")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Prédécesseur majoré par l’entier",
            "Le prédécesseur d'un entier est ≤ à cet entier",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Предыдущее целое не больше исходного",
            "Предыдущее целое ≤ исходного целого",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Predecesor acotado por el entero",
            "El predecesor de un entero es ≤ al entero",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "السابق لا يتجاوز العدد الصحيح",
            "سابق العدد الصحيح ≤ ذلك العدد",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "前の整数と元の整数の弱い大小関係",
            "直前の整数はその整数以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "이전 정수와 원래 정수의 비엄격 순서",
            "정수의 이전 값은 그 정수 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Số nguyên trước không lớn hơn số ban đầu",
            "Số nguyên liền trước ≤ số nguyên đó",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl IntegerDiffAtLeastOneLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Integer gap ≥ 1",
            "Distinct integers differ by at least one",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "整数间隔 ≥ 1",
            "不同整数至少相差 1",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "整數差距 ≥ 1",
            "不同整數至少相差一",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Écart entier ≥ 1",
            "Des entiers distincts diffèrent d'au moins un",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Целочисленный промежуток ≥ 1",
            "Различные целые отличаются хотя бы на единицу",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Brecha entera ≥ 1",
            "Enteros distintos difieren al menos en uno",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فجوة صحيحة ≥ 1",
            "الأعداد الصحيحة المختلفة تختلف بواحد على الأقل",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "整数の差 ≥ 1",
            "異なる整数は少なくとも一だけ異なります",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "정수 간격 ≥ 1",
            "서로 다른 정수는 적어도 1만큼 차이납니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khoảng cách nguyên ≥ 1",
            "Các số nguyên khác nhau chênh ít nhất một",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetMaxMemberLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "max member ≤",
            "Every member of a finite set is ≤ its maximum",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "元素 ≤ 最大值",
            "有限集每个元素 ≤ 其最大值",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "成員 ≤ 最大值",
            "有限集合每個成員 ≤ 其最大值",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Membre ≤ maximum",
            "Chaque membre d'un ensemble fini est ≤ à son maximum",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Элемент ≤ максимум",
            "Каждый элемент конечного множества ≤ его максимума",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Miembro ≤ máximo",
            "Cada miembro de conjunto finito es ≤ a su máximo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عنصر ≤ القيمة العظمى",
            "كل عنصر من مجموعة منتهية ≤ قيمتها العظمى",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "要素 ≤ 最大値",
            "有限集合の各要素はその最大値以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "원소 ≤ 최댓값",
            "유한 집합의 모든 원소는 최댓값 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Phần tử ≤ lớn nhất",
            "Mọi phần tử của tập hữu hạn ≤ giá trị lớn nhất",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetMinMemberLeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "min ≤ member",
            "The minimum of a finite set is ≤ every member",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "最小值 ≤ 元素",
            "有限集最小值 ≤ 每个元素",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "最小值 ≤ 成員",
            "有限集合的最小值 ≤ 每個成員",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Minimum ≤ membre",
            "Le minimum d'un ensemble fini est ≤ à chaque membre",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Минимум ≤ элемент",
            "Минимум конечного множества ≤ каждого элемента",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Mínimo ≤ miembro",
            "El mínimo de conjunto finito es ≤ a cada miembro",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "القيمة الصغرى ≤ عنصر",
            "القيمة الصغرى لمجموعة منتهية ≤ كل عنصر",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "最小値 ≤ 要素",
            "有限集合の最小値は各要素以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "최솟값 ≤ 원소",
            "유한 집합의 최솟값은 모든 원소 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Nhỏ nhất ≤ phần tử",
            "Giá trị nhỏ nhất của tập hữu hạn ≤ mọi phần tử",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetSizeUnionLeSumBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Cardinality of a union bounded by the sum",
            "Finite-set union size is at most the sum of sizes",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "并集基数不大于基数之和",
            "有限并集大小不超过各大小之和",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "聯集基數不大於基數之和",
            "有限集合聯集大小至多為大小之和",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Cardinal de l’union majoré par la somme",
            "La taille d'une union finie ne dépasse pas la somme des tailles",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Мощность объединения не больше суммы мощностей",
            "Размер объединения конечных множеств не больше суммы размеров",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cardinalidad de la unión acotada por la suma",
            "El tamaño de unión finita no supera la suma de tamaños",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدد عناصر الاتحاد لا يتجاوز مجموع العددين",
            "حجم اتحاد مجموعتين منتهيتين لا يزيد على مجموع حجميهما",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "和集合の要素数と要素数の和の上界",
            "有限集合の和の大きさは各大きさの和以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "합집합 원소 수의 합 상계",
            "유한 집합의 합집합 크기는 각 크기의 합 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lực lượng của hợp không vượt quá tổng",
            "Kích thước hợp tập hữu hạn không vượt tổng kích thước",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "|codomain| ≤ |domain|",
            "A surjection implies the codomain is no larger than the domain",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "|值域| ≤ |定义域|",
            "满射蕴含值域不大于定义域",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "|陪域| ≤ |定義域|",
            "滿射推出陪域不大於定義域",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "|codomaine| ≤ |domaine|",
            "Une surjection implique que le codomaine n'est pas plus grand que le domaine",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "|область_значений| ≤ |область_определения|",
            "Сюръекция означает, что область значений не больше области определения",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "|codominio| ≤ |dominio|",
            "Una sobreyección implica que el codominio no es mayor que el dominio",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "|المجال_المقابل| ≤ |المجال|",
            "الشمول يستلزم أن المجال المقابل لا يزيد على المجال",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "|終域| ≤ |定義域|",
            "全射から終域は定義域より大きくないことを導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "|공역| ≤ |정의역|",
            "전사로 공역이 정의역보다 크지 않음을 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "|đối_miền| ≤ |miền_xác_định|",
            "Toàn ánh suy ra đối miền không lớn hơn miền xác định",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl OrderFlipMulMinusOneToLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Order flip by ×(-1)",
            "Multiplying by -1 reverses the inequality",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "乘以 -1 反转不等式",
            "两边同乘 -1 后不等式方向相反",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "乘以 -1 反轉序",
            "乘以 -1 反轉不等式方向",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inversion d'ordre par ×(-1)",
            "Multiplier par -1 inverse l'inégalité",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обращение порядка при ×(-1)",
            "Умножение на -1 обращает неравенство",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inversión de orden por ×(-1)",
            "Multiplicar por -1 invierte la desigualdad",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عكس الترتيب بالضرب في (-1)",
            "الضرب في -1 يعكس المتباينة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "×(-1) による順序反転",
            "-1 を掛けると不等号が反転します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "×(-1)에 의한 순서 반전",
            "-1을 곱하면 부등호가 반전됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đảo thứ tự bởi ×(-1)",
            "Nhân với -1 đảo chiều bất đẳng thức",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl OrderSignFromNegativeLiteralBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Sign from negative bound",
            "A negative literal bound forces the stated order/sign",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由负上界得符号",
            "负的字面上界推出所述序/符号关系",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由負數界得符號",
            "負字面值界推出所述序或符號",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Signe depuis une borne négative",
            "Une borne littérale négative impose l'ordre ou le signe indiqué",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Знак из отрицательной границы",
            "Отрицательная литеральная граница задаёт указанный порядок или знак",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Signo desde cota negativa",
            "Una cota literal negativa fuerza el orden o signo indicado",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "إشارة من حد سالب",
            "حد حرفي سالب يفرض الترتيب أو الإشارة المذكورة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "負の境界から符号",
            "負のリテラルの境界から指定された順序または符号を導きます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "음수 경계로 부호",
            "음수 리터럴 경계로 명시된 순서 또는 부호를 도출합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Dấu từ cận âm",
            "Cận literal âm suy ra thứ tự hoặc dấu đã nêu",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl FromKnownGreaterEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Known converse order",
            "The opposite-direction comparison is already known",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "已知反向序关系",
            "引用已知的反向比较事实",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("已知反向序關係", "反方向比較已知")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ordre inverse connu",
            "La comparaison dans le sens opposé est déjà connue",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Известный обратный порядок",
            "Сравнение в обратном направлении уже известно",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Orden inverso conocido",
            "La comparación en sentido opuesto ya es conocida",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ترتيب عكسي معلوم",
            "المقارنة في الاتجاه المعاكس معلومة بالفعل",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の逆向きの順序",
            "逆向きの比較は既知です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 역방향 순서",
            "반대 방향의 비교가 이미 알려져 있습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thứ tự đảo chiều đã biết",
            "So sánh theo chiều ngược đã biết",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}

impl PositiveCommonDivisorLeGcdBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Common positive divisor bound",
            "A positive divisor of both inputs is at most their positive gcd",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "公共正因子上界",
            "两个整数的公共正因子不超过它们的正最大公因子",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "公共正因數上界",
            "兩個整數的公共正因數不超過它們的正最大公因數",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne du diviseur positif commun",
            "Un diviseur positif des deux entiers est inférieur ou égal à leur PGCD positif",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Граница общего положительного делителя",
            "Общий положительный делитель не превосходит положительный НОД",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cota del divisor positivo común",
            "Un divisor positivo de ambos enteros no supera su máximo común divisor positivo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "حد القاسم الموجب المشترك",
            "القاسم الموجب المشترك للعددين لا يتجاوز القاسم المشترك الأكبر الموجب",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "正の公約数の上界",
            "両整数の正の公約数は正の最大公約数以下です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "양의 공약수 상한",
            "두 정수의 양의 공약수는 양의 최대공약수 이하입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Cận của ước chung dương",
            "Ước chung dương của hai số nguyên không vượt quá ước chung lớn nhất dương",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}
