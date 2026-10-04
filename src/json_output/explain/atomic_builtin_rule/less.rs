//! Explain + cite for `LessFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{
    FromKnownGreaterBuiltinRuleProof,
    LessFactSearchProofByBuiltinRule, FiniteSetSizeProperSubsetLtBuiltinRuleProof, AddLeftCongruenceStrictBuiltinRuleProof,
    AddRightCongruenceStrictBuiltinRuleProof, ArccotPrincipalLowerBoundBuiltinRuleProof,
    ArccotPrincipalUpperBoundBuiltinRuleProof, ArctanPrincipalLowerBoundBuiltinRuleProof,
    ArctanPrincipalUpperBoundBuiltinRuleProof, ClosedNumericComparisonBuiltinRuleProof,
    DivByGtOneLessSelfBuiltinRuleProof, DivMonotoneStrictSameNegDivisorBuiltinRuleProof,
    DivMonotoneStrictSamePosDivisorBuiltinRuleProof, EvenPowPositiveFromNonzeroBuiltinRuleProof,
    LessFromPosDifferenceBuiltinRuleProof, LessTransitivityBuiltinRuleProof,
    LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof,
    LogOrderPreservingStrictBuiltinRuleProof, LogPositiveFromBaseAndArgGtOneBuiltinRuleProof,
    ModRemainderStrictUpperBoundBuiltinRuleProof, MulLeftPositiveMonotoneStrictBuiltinRuleProof,
    MulRightPositiveMonotoneStrictBuiltinRuleProof, NumericLowerBoundWeakenLtBuiltinRuleProof,
    NumericUpperBoundWeakenLtBuiltinRuleProof, PosDifferenceFromLessBuiltinRuleProof,
    PositiveEvenGtOneBuiltinRuleProof, PowPositiveFromPositiveBaseBuiltinRuleProof,
    ProductBothPositiveBuiltinRuleProof, SqrtMonotoneIncreasingBuiltinRuleProof,
    SqrtPositiveBuiltinRuleProof, SubtractOneLessBuiltinRuleProof,
    SubtractPositiveClosedLessBuiltinRuleProof, SumBothPositiveBuiltinRuleProof,
    SumLeftNonnegativeRightStrictBuiltinRuleProof, SumLeftStrictRightNonnegativeBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromPositiveLiteralBoundBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl LessFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_en(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_en(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_en(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "Exact pi coefficient order",
                "pi is positive and the exact left rational coefficient is smaller",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_en(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_en(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_en(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_en(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_en(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_en(),
            Self::SumBothPositive(p) => p.rule_id_and_message_en(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_en(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_en(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_en(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_en(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_en(),
            Self::SqrtPositive(p) => p.rule_id_and_message_en(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_en(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_en(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_en(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_en(),
            Self::LessTransitivity(p) => p.rule_id_and_message_en(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_en(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_en(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_en(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_en(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_en(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_en(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_en(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_en(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_en(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_en(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_en(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_en(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_en(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_en(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_en(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_en(),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_zh(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_zh(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_zh(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "pi 系数精确比较",
                "pi 为正且左边的精确有理系数更小",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_zh(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_zh(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_zh(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_zh(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_zh(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_zh(),
            Self::SumBothPositive(p) => p.rule_id_and_message_zh(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_zh(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_zh(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_zh(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_zh(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_zh(),
            Self::SqrtPositive(p) => p.rule_id_and_message_zh(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_zh(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_zh(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_zh(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_zh(),
            Self::LessTransitivity(p) => p.rule_id_and_message_zh(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_zh(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_zh(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_zh(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_zh(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_zh(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_zh(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_zh(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_zh(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_zh(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_zh(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_zh(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_zh(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_zh(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_zh(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_zh(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_zh(),
        }
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_zh_hant(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_zh_hant(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_zh_hant(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "精確 pi 係數序",
                "pi 為正且精確左有理係數較小",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_zh_hant(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_zh_hant(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_zh_hant(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_zh_hant(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_zh_hant(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_zh_hant(),
            Self::SumBothPositive(p) => p.rule_id_and_message_zh_hant(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_zh_hant(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_zh_hant(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_zh_hant(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_zh_hant(),
            Self::SqrtPositive(p) => p.rule_id_and_message_zh_hant(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_zh_hant(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_zh_hant(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_zh_hant(),
            Self::LessTransitivity(p) => p.rule_id_and_message_zh_hant(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_zh_hant(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_zh_hant(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_zh_hant(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_zh_hant(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_zh_hant(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_zh_hant(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_zh_hant(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_zh_hant(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_zh_hant(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_zh_hant(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_zh_hant(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_zh_hant(),
        }
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_fr(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_fr(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_fr(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "Ordre exact des coefficients de pi",
                "pi est positif et le coefficient rationnel exact de gauche est inférieur",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_fr(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_fr(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_fr(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_fr(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_fr(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_fr(),
            Self::SumBothPositive(p) => p.rule_id_and_message_fr(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_fr(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_fr(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_fr(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_fr(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_fr(),
            Self::SqrtPositive(p) => p.rule_id_and_message_fr(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_fr(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_fr(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_fr(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_fr(),
            Self::LessTransitivity(p) => p.rule_id_and_message_fr(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_fr(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_fr(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_fr(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_fr(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_fr(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_fr(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_fr(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_fr(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_fr(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_fr(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_fr(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_fr(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_fr(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_fr(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_fr(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_fr(),
        }
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_ru(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ru(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ru(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "Точный порядок коэффициентов pi",
                "pi положительно, и точный левый рациональный коэффициент меньше",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_ru(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_ru(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_ru(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_ru(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_ru(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_ru(),
            Self::SumBothPositive(p) => p.rule_id_and_message_ru(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_ru(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_ru(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_ru(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_ru(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_ru(),
            Self::SqrtPositive(p) => p.rule_id_and_message_ru(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_ru(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_ru(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_ru(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_ru(),
            Self::LessTransitivity(p) => p.rule_id_and_message_ru(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_ru(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_ru(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_ru(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_ru(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_ru(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_ru(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_ru(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_ru(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_ru(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ru(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ru(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ru(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ru(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_ru(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_ru(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_ru(),
        }
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_es(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_es(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_es(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "Orden exacto de coeficientes de pi",
                "pi es positivo y el coeficiente racional exacto izquierdo es menor",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_es(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_es(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_es(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_es(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_es(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_es(),
            Self::SumBothPositive(p) => p.rule_id_and_message_es(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_es(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_es(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_es(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_es(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_es(),
            Self::SqrtPositive(p) => p.rule_id_and_message_es(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_es(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_es(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_es(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_es(),
            Self::LessTransitivity(p) => p.rule_id_and_message_es(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_es(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_es(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_es(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_es(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_es(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_es(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_es(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_es(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_es(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_es(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_es(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_es(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_es(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_es(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_es(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_es(),
        }
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_ar(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ar(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ar(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "ترتيب دقيق لمعاملات pi",
                "pi موجب والمعامل النسبي الدقيق الأيسر أصغر",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_ar(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_ar(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_ar(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_ar(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_ar(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_ar(),
            Self::SumBothPositive(p) => p.rule_id_and_message_ar(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_ar(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_ar(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_ar(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_ar(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_ar(),
            Self::SqrtPositive(p) => p.rule_id_and_message_ar(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_ar(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_ar(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_ar(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_ar(),
            Self::LessTransitivity(p) => p.rule_id_and_message_ar(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_ar(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_ar(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_ar(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_ar(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_ar(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_ar(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_ar(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_ar(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_ar(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ar(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ar(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ar(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ar(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_ar(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_ar(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_ar(),
        }
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_ja(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ja(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ja(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "正確な pi 係数の順序",
                "pi は正で、正確な左の有理係数が小さいです",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_ja(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_ja(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_ja(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_ja(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_ja(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_ja(),
            Self::SumBothPositive(p) => p.rule_id_and_message_ja(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_ja(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_ja(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_ja(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_ja(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_ja(),
            Self::SqrtPositive(p) => p.rule_id_and_message_ja(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_ja(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_ja(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_ja(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_ja(),
            Self::LessTransitivity(p) => p.rule_id_and_message_ja(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_ja(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_ja(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_ja(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_ja(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_ja(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_ja(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_ja(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_ja(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_ja(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ja(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ja(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ja(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ja(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_ja(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_ja(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_ja(),
        }
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_ko(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ko(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ko(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "정확한 pi 계수 순서",
                "pi는 양수이고 정확한 왼쪽 유리수 계수가 더 작습니다",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_ko(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_ko(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_ko(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_ko(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_ko(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_ko(),
            Self::SumBothPositive(p) => p.rule_id_and_message_ko(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_ko(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_ko(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_ko(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_ko(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_ko(),
            Self::SqrtPositive(p) => p.rule_id_and_message_ko(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_ko(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_ko(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_ko(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_ko(),
            Self::LessTransitivity(p) => p.rule_id_and_message_ko(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_ko(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_ko(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_ko(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_ko(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_ko(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_ko(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_ko(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_ko(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_ko(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ko(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ko(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ko(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ko(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_ko(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_ko(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_ko(),
        }
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message_vi(),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_vi(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_vi(),
            Self::PiMultipleComparison(_) => text(
                "PiMultipleComparison",
                "Thứ tự hệ số pi chính xác",
                "pi dương và hệ số hữu tỉ chính xác bên trái nhỏ hơn",
            ),
            Self::SubtractOneLess(p) => p.rule_id_and_message_vi(),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message_vi(),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message_vi(),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message_vi(),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message_vi(),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message_vi(),
            Self::SumBothPositive(p) => p.rule_id_and_message_vi(),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message_vi(),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message_vi(),
            Self::ProductBothPositive(p) => p.rule_id_and_message_vi(),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message_vi(),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message_vi(),
            Self::SqrtPositive(p) => p.rule_id_and_message_vi(),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message_vi(),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message_vi(),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message_vi(),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message_vi(),
            Self::LessTransitivity(p) => p.rule_id_and_message_vi(),
            Self::LessFromPosDifference(p) => p.rule_id_and_message_vi(),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message_vi(),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message_vi(),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message_vi(),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message_vi(),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message_vi(),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message_vi(),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message_vi(),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message_vi(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_vi(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_vi(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_vi(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_vi(),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message_vi(),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message_vi(),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message_vi(),
        }
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownGreater(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::LessTransitivity(_) => None,
            Self::LessFromPosDifference(p) => p.premise_proof.cite_fact_id(),
            Self::PosDifferenceFromLess(p) => p.premise_proof.cite_fact_id(),
            Self::NumericLowerBoundWeakenLt(p) => Some(p.cite_fact_id),
            Self::NumericUpperBoundWeakenLt(p) => Some(p.cite_fact_id),
            Self::OrderSignFromPositiveLiteralBound(p) => Some(p.cite_fact_id),
            Self::OrderFlipMulMinusOne(p) => p.premise_proof.cite_fact_id(),
            _ => None,
        }
    }
}

impl FiniteSetSizeProperSubsetLtBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "Proper finite subset cardinality",
            "A proper subset of a finite set has strictly smaller cardinality",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "有限真子集的基数严格更小",
            "有限集合的真子集具有严格更小的基数",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "有限真子集基數",
            "有限集合的真子集基數嚴格較小",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "Cardinal d'un sous-ensemble propre fini",
            "Un sous-ensemble propre d'un ensemble fini a un cardinal strictement inférieur",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "Мощность конечного собственного подмножества",
            "Собственное подмножество конечного множества имеет строго меньшую мощность",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "Cardinalidad de subconjunto propio finito",
            "Un subconjunto propio de conjunto finito tiene cardinalidad estrictamente menor",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "عدد عناصر مجموعة جزئية حقيقية منتهية",
            "المجموعة الجزئية الحقيقية لمجموعة منتهية عدد عناصرها أصغر تمامًا",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "有限真部分集合の濃度",
            "有限集合の真部分集合の濃度は厳密に小さいです",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "유한 진부분집합의 기수",
            "유한 집합의 진부분집합 기수는 엄격히 작습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeProperSubsetLt",
            "Lực lượng tập con thực sự hữu hạn",
            "Tập con thực sự của tập hữu hạn có lực lượng nhỏ hơn nghiêm ngặt",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Closed numeric comparison",
            "Both sides are closed numbers and compare as stated",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "封闭数值比较",
            "两边都是可计算的数，并满足所述比较",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "封閉數值比較",
            "兩邊為封閉數值且符合所述比較",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Comparaison numérique fermée",
            "Les deux membres sont des nombres fermés et satisfont la comparaison indiquée",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Сравнение замкнутых числовых выражений",
            "Обе части являются замкнутыми числами и удовлетворяют указанному сравнению",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Comparación numérica cerrada",
            "Ambos lados son números cerrados y cumplen la comparación indicada",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "مقارنة عددية مغلقة",
            "الطرفان عددان مغلقان ويحققان المقارنة المذكورة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "閉じた数値式の比較",
            "両辺は閉じた数値であり、指定された比較を満たします",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "닫힌 수치 식 비교",
            "양변은 닫힌 수이며 명시된 비교를 만족합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "So sánh số đóng",
            "Hai vế là số đóng và thỏa so sánh đã nêu",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl SubtractOneLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "Subtracting one strictly decreases a real number",
            "Subtracting one yields a strictly smaller value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubtractOneLess", "实数减一后严格变小", "减一得到严格更小的值")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("SubtractOneLess", "實數減一後嚴格變小", "減一得嚴格較小值")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "Soustraire un diminue strictement un réel",
            "Soustraire un donne une valeur strictement inférieure",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "Вычитание единицы строго уменьшает вещественное число",
            "Вычитание единицы даёт строго меньшее значение",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "Restar uno disminuye estrictamente un real",
            "Restar uno da un valor estrictamente menor",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "طرح واحد ينقص العدد الحقيقي بشكل صارم",
            "طرح واحد يعطي قيمة أصغر تمامًا",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "実数から一を引くと厳密に小さくなる",
            "一を引くと厳密に小さい値になります",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "실수에서 일을 빼면 엄격히 작아짐",
            "1을 빼면 엄격히 작은 값이 됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "Trừ một làm số thực giảm nghiêm ngặt",
            "Trừ một cho giá trị nhỏ hơn nghiêm ngặt",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl SubtractPositiveClosedLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "Subtract a positive constant",
            "Subtracting a closed exact positive value yields a smaller real value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "减去正的常数",
            "实数减去可精确计算的正数，结果严格更小",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "減去正常數",
            "減去封閉精確正值得較小實數值",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "Soustraction d'une constante positive",
            "Soustraire une valeur positive fermée exacte donne un réel plus petit",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
                "SubtractPositiveClosedLess",
                "Вычитание положительной константы",
                "Вычитание точного замкнутого положительного значения даёт меньшее вещественное значение",
            )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "Restar constante positiva",
            "Restar un valor positivo cerrado exacto da un real menor",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "طرح ثابت موجب",
            "طرح قيمة موجبة مغلقة دقيقة يعطي قيمة حقيقية أصغر",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "正の定数の減算",
            "正確な閉じた正値を引くと小さい実数値になります",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "양의 상수 빼기",
            "정확한 닫힌 양의 값을 빼면 더 작은 실수 값이 됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "SubtractPositiveClosedLess",
            "Trừ hằng dương",
            "Trừ giá trị dương đóng chính xác cho giá trị thực nhỏ hơn",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ArctanPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "arctan lower bound",
            "arctan stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "arctan 下界",
            "arctan 落在其主值下界内",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "arctan 下界",
            "arctan 不低於主值下界",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "Borne inférieure de arctan",
            "arctan respecte sa borne principale inférieure",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "Нижняя граница arctan",
            "arctan не ниже своей главной нижней границы",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "Cota inferior de arctan",
            "arctan respeta su cota principal inferior",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "حد أدنى لـ arctan",
            "arctan يبقى ضمن حده الرئيسي الأدنى",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "arctan の下界",
            "arctan は主値の下界以上です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "arctan 하한",
            "arctan는 주값 하한 이상입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "Cận dưới arctan",
            "arctan giữ trong cận dưới chính",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ArctanPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "arctan upper bound",
            "arctan stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "arctan 上界",
            "arctan 落在其主值上界内",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "arctan 上界",
            "arctan 不高於主值上界",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "Borne supérieure de arctan",
            "arctan respecte sa borne principale supérieure",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "Верхняя граница arctan",
            "arctan не выше своей главной верхней границы",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "Cota superior de arctan",
            "arctan respeta su cota principal superior",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "حد أعلى لـ arctan",
            "arctan يبقى ضمن حده الرئيسي الأعلى",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "arctan の上界",
            "arctan は主値の上界以下です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "arctan 상한",
            "arctan는 주값 상한 이하입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "Cận trên arctan",
            "arctan giữ trong cận trên chính",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ArccotPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "arccot lower bound",
            "arccot stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "arccot 下界",
            "arccot 落在其主值下界内",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "arccot 下界",
            "arccot 不低於主值下界",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "Borne inférieure de arccot",
            "arccot respecte sa borne principale inférieure",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "Нижняя граница arccot",
            "arccot не ниже своей главной нижней границы",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "Cota inferior de arccot",
            "arccot respeta su cota principal inferior",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "حد أدنى لـ arccot",
            "arccot يبقى ضمن حده الرئيسي الأدنى",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "arccot の下界",
            "arccot は主値の下界以上です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "arccot 하한",
            "arccot는 주값 하한 이상입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "Cận dưới arccot",
            "arccot giữ trong cận dưới chính",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ArccotPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "arccot upper bound",
            "arccot stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "arccot 上界",
            "arccot 落在其主值上界内",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "arccot 上界",
            "arccot 不高於主值上界",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "Borne supérieure de arccot",
            "arccot respecte sa borne principale supérieure",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "Верхняя граница arccot",
            "arccot не выше своей главной верхней границы",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "Cota superior de arccot",
            "arccot respeta su cota principal superior",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "حد أعلى لـ arccot",
            "arccot يبقى ضمن حده الرئيسي الأعلى",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "arccot の上界",
            "arccot は主値の上界以下です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "arccot 상한",
            "arccot는 주값 상한 이하입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "Cận trên arccot",
            "arccot giữ trong cận trên chính",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl SumBothPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "Sum of positives > 0",
            "A sum of positive terms is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumBothPositive", "正数和 > 0", "正项之和为正")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("SumBothPositive", "正數和 > 0", "正項的和為正")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "Somme de positifs > 0",
            "Une somme de termes positifs est positive",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "Сумма положительных > 0",
            "Сумма положительных членов положительна",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "Suma de positivos > 0",
            "Una suma de términos positivos es positiva",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "مجموع الموجبات > 0",
            "مجموع حدود موجبة موجب",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text("SumBothPositive", "正数の和 > 0", "正の項の和は正です")
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "양수의 합 > 0",
            "양의 항의 합은 양수입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "Tổng số dương > 0",
            "Tổng các hạng dương là dương",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl SumLeftStrictRightNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "pos + nonneg > 0",
            "Strictly positive plus nonnegative is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "正 + 非负 > 0",
            "严格正加非负为正",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "正數 + 非負數 > 0",
            "嚴格正數加非負數為正",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "Positif + non-négatif > 0",
            "Strictement positif plus non-négatif est positif",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "Положительное + неотрицательное > 0",
            "Строго положительное плюс неотрицательное положительно",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "Positivo + no negativo > 0",
            "Estrictamente positivo más no negativo es positivo",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "الموجب + غير السالب > 0",
            "الموجب تمامًا زائد غير السالب موجب",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "正数 + 非負数 > 0",
            "厳密な正数と非負数の和は正です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "양수 + 비음수 > 0",
            "엄격한 양수와 비음수의 합은 양수입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "Dương + không âm > 0",
            "Dương nghiêm ngặt cộng không âm là dương",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl SumLeftNonnegativeRightStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "nonneg + pos > 0",
            "Nonnegative plus strictly positive is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "非负 + 正 > 0",
            "非负加严格正为正",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "非負數 + 正數 > 0",
            "非負數加嚴格正數為正",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "Non-négatif + positif > 0",
            "Non-négatif plus strictement positif est positif",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "Неотрицательное + положительное > 0",
            "Неотрицательное плюс строго положительное положительно",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "No negativo + positivo > 0",
            "No negativo más estrictamente positivo es positivo",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "غير السالب + الموجب > 0",
            "غير السالب زائد الموجب تمامًا موجب",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "非負数 + 正数 > 0",
            "非負数と厳密な正数の和は正です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "비음수 + 양수 > 0",
            "비음수와 엄격한 양수의 합은 양수입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "Không âm + dương > 0",
            "Không âm cộng dương nghiêm ngặt là dương",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ProductBothPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "Product of positives > 0",
            "A product of positive factors is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductBothPositive", "正数积 > 0", "正因子之积为正")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("ProductBothPositive", "正數乘積 > 0", "正因子的乘積為正")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "Produit de positifs > 0",
            "Un produit de facteurs positifs est positif",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "Произведение положительных > 0",
            "Произведение положительных множителей положительно",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "Producto de positivos > 0",
            "Un producto de factores positivos es positivo",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "حاصل ضرب الموجبات > 0",
            "حاصل ضرب عوامل موجبة موجب",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "正数の積 > 0",
            "正の因子の積は正です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "양수의 곱 > 0",
            "양의 인자의 곱은 양수입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "Tích số dương > 0",
            "Tích các thừa số dương là dương",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl EvenPowPositiveFromNonzeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "Even power > 0",
            "An even power of a checked nonzero real base is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "偶次幂 > 0",
            "已验证的非零实数底数的偶次幂为正",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "偶數次方 > 0",
            "經驗證非零實數底數的偶數次方為正",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "Puissance paire > 0",
            "Une puissance paire d'une base réelle non nulle vérifiée est positive",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "Чётная степень > 0",
            "Чётная степень проверенного ненулевого вещественного основания положительна",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "Potencia par > 0",
            "Una potencia par de base real no nula comprobada es positiva",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "قوة زوجية > 0",
            "القوة الزوجية لأساس حقيقي غير صفري متحقق منه موجبة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "偶数乗 > 0",
            "検証済みの非ゼロ実数の底の偶数乗は正です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "짝수 거듭제곱 > 0",
            "검증된 0이 아닌 실수 밑의 짝수 거듭제곱은 양수입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "Lũy thừa chẵn > 0",
            "Lũy thừa chẵn của cơ số thực khác không đã kiểm tra là dương",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl PowPositiveFromPositiveBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "pow > 0 (pos base)",
            "A positive base raised to a real power is positive where defined",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "幂 > 0（正底）",
            "正底数的实数次幂在有定义时为正",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "正底數的冪 > 0",
            "正底數的實數次方在定義成立時為正",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "Puissance > 0 (base positive)",
            "Une base positive à une puissance réelle est positive là où elle est définie",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "Степень > 0 (положительное основание)",
            "Положительное основание в вещественной степени положительно там, где определено",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "Potencia > 0 (base positiva)",
            "Una base positiva elevada a potencia real es positiva donde está definida",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "قوة > 0 (أساس موجب)",
            "الأساس الموجب مرفوعًا لقوة حقيقية موجب حيث يكون معرّفًا",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "冪 > 0（正の底）",
            "正の底の実数乗は定義されるところで正です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "거듭제곱 > 0(양수 밑)",
            "양의 밑의 실수 거듭제곱은 정의되는 곳에서 양수입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "Lũy thừa > 0 (cơ số dương)",
            "Cơ số dương nâng lũy thừa thực là dương khi xác định",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl SqrtPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "Positivity of the square root of a positive real",
            "Square root of a positive value is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtPositive", "正实数的平方根为正", "正数的平方根为正")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("SqrtPositive", "正實數的平方根為正", "正值的平方根為正")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "Positivité de la racine d’un réel positif",
            "La racine carrée d'un positif est positive",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "Положительность корня положительного числа",
            "Квадратный корень положительного значения положителен",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "Positividad de la raíz de un real positivo",
            "La raíz cuadrada de un positivo es positiva",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text("SqrtPositive", "إيجابية جذر عدد حقيقي موجب", "الجذر التربيعي لقيمة موجبة موجب")
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text("SqrtPositive", "正の実数の平方根の正値性", "正の値の平方根は正です")
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text("SqrtPositive", "양의 실수 제곱근의 양수성", "양의 값의 제곱근은 양수입니다")
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "Căn bậc hai của số thực dương là dương",
            "Căn bậc hai của giá trị dương là dương",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl SqrtMonotoneIncreasingBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "√ monotone strict",
            "Square root is strictly increasing on [0,∞)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "√ 严格单调",
            "平方根在 [0,∞) 上严格递增",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "平方根嚴格單調性",
            "平方根在 [0,∞) 上嚴格遞增",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "Monotonie stricte de √",
            "La racine carrée est strictement croissante sur [0,∞)",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "Строгая монотонность √",
            "Квадратный корень строго возрастает на [0,∞)",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "Monotonía estricta de √",
            "La raíz cuadrada es estrictamente creciente en [0,∞)",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "رتابة صارمة لـ √",
            "الجذر التربيعي متزايد تمامًا على [0,∞)",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "√ の狭義単調性",
            "平方根は [0,∞) 上で狭義増加です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "√ 엄격한 단조성",
            "제곱근은 [0,∞)에서 엄격히 증가합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "Đơn điệu nghiêm ngặt của √",
            "Căn bậc hai tăng nghiêm ngặt trên [0,∞)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl LogOrderPreservingStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "log order strict",
            "Log with base > 1 preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "对数严格保序",
            "底大于 1 的对数保持严格序",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "對數嚴格序",
            "底數 > 1 的對數保持嚴格序",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "Ordre strict du logarithme",
            "Le logarithme de base > 1 préserve l'ordre strict",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "Строгий порядок логарифма",
            "Логарифм с основанием > 1 сохраняет строгий порядок",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "Orden estricto del logaritmo",
            "El logaritmo de base > 1 conserva el orden estricto",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "ترتيب صارم للوغاريتم",
            "اللوغاريتم بأساس > 1 يحفظ الترتيب الصارم",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "対数の狭義順序",
            "底 > 1 の対数は狭義順序を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "로그의 엄격한 순서",
            "밑 > 1인 로그는 엄격한 순서를 보존합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "Thứ tự nghiêm ngặt của logarit",
            "Logarit cơ số > 1 bảo toàn thứ tự nghiêm ngặt",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl LogPositiveFromBaseAndArgGtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "Positive logarithm for base and argument above one",
            "For a base greater than one, the logarithm of an argument greater than one is positive: a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "底和真数均大于一时对数为正",
            "底大于一时，大于一的真数的对数为正，即 a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "底和真數均大於一時對數為正",
            "底大於一時，大於一的真數的對數為正，即 a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "Logarithme positif pour une base et un argument supérieurs à un",
            "Pour une base supérieure à un, le logarithme d’un argument supérieur à un est positif: a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "Положительный логарифм при основании и аргументе больше единицы",
            "При основании больше единицы логарифм аргумента больше единицы положителен: a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "Logaritmo positivo con base y argumento mayores que uno",
            "Con base mayor que uno, el logaritmo de un argumento mayor que uno es positivo: a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "لوغاريتم موجب لأساس ووسيط أكبر من واحد",
            "عندما يكون الأساس أكبر من واحد يكون لوغاريتم وسيط أكبر من واحد موجبًا: a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "底と引数が一より大きい場合の対数の正値性",
            "底が一より大きいとき、一より大きい引数の対数は正です：a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "밑과 인수가 일보다 클 때 로그의 양수성",
            "밑이 일보다 크면 일보다 큰 인수의 로그는 양수입니다：a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "Logarit dương khi cơ số và đối số lớn hơn một",
            "Với cơ số lớn hơn một, logarit của đối số lớn hơn một là dương: a > 1 ∧ x > 1 ⇒ log_a(x) > 0",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "Negative logarithm for base above one and argument between zero and one",
            "Log with base > 1 is negative on (0,1)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "底大于一且真数介于零和一时对数为负",
            "底大于 1 时对数在 (0,1) 上为负",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "底大於一且真數介於零和一時對數為負",
            "底數 > 1 的對數在 (0,1) 上為負",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "Logarithme négatif avec base supérieure à un et argument entre zéro et un",
            "Le logarithme de base > 1 est négatif sur (0,1)",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "Отрицательный логарифм при основании больше единицы и аргументе между нулём и единицей",
            "Логарифм с основанием > 1 отрицателен на (0,1)",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "Logaritmo negativo con base mayor que uno y argumento entre cero y uno",
            "El logaritmo de base > 1 es negativo en (0,1)",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "لوغاريتم سالب لأساس أكبر من واحد ووسيط بين صفر وواحد",
            "اللوغاريتم بأساس > 1 سالب على (0,1)",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "底が一より大きく引数が零と一の間の場合の負の対数",
            "底 > 1 の対数は (0,1) 上で負です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "밑이 일보다 크고 인수가 영과 일 사이일 때 음의 로그",
            "밑 > 1인 로그는 (0,1)에서 음수입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "Logarit âm khi cơ số lớn hơn một và đối số giữa không và một",
            "Logarit cơ số > 1 âm trên (0,1)",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl LessTransitivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessTransitivity",
            "< transitivity",
            "Strict less is transitive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LessTransitivity", "< 传递性", "< 具有传递性")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("LessTransitivity", "< 遞移性", "嚴格小於具遞移性")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "LessTransitivity",
            "Transitivité de <",
            "La relation strictement inférieure est transitive",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "LessTransitivity",
            "Транзитивность <",
            "Строгое отношение меньше транзитивно",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "LessTransitivity",
            "Transitividad de <",
            "Menor estricto es transitivo",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text("LessTransitivity", "تعدي <", "علاقة أصغر الصارمة متعدية")
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "LessTransitivity",
            "< の推移性",
            "狭義の小なり関係は推移的です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text("LessTransitivity", "< 추이성", "엄격한 작음은 추이적입니다")
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "LessTransitivity",
            "Tính bắc cầu của <",
            "Nhỏ hơn nghiêm ngặt có tính bắc cầu",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl LessFromPosDifferenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "Positive difference implies strict order",
            "The Positive difference implies strict order law gives: 0 < b-a ⇒ a < b",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LessFromPosDifference", "差为正推出严格大小关系", "差为正推出严格大小关系可写为：0 < b-a ⇒ a < b")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("LessFromPosDifference", "差為正推出嚴格大小關係", "差為正推出嚴格大小關係可寫為：0 < b-a ⇒ a < b")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "Différence positive et ordre strict",
            "La propriété « Différence positive et ordre strict » donne: 0 < b-a ⇒ a < b",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "Положительная разность даёт строгий порядок",
            "Свойство «Положительная разность даёт строгий порядок» выражается равенством: 0 < b-a ⇒ a < b",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "Diferencia positiva implica orden estricto",
            "La propiedad «Diferencia positiva implica orden estricto» se expresa como: 0 < b-a ⇒ a < b",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text("LessFromPosDifference", "الفرق الموجب يستلزم ترتيبًا صارمًا", "تُكتب خاصية «الفرق الموجب يستلزم ترتيبًا صارمًا» كما يلي: 0 < b-a ⇒ a < b")
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text("LessFromPosDifference", "正の差から得られる厳密な大小関係", "正の差から得られる厳密な大小関係は次の式で表されます：0 < b-a ⇒ a < b")
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text("LessFromPosDifference", "양의 차에서 얻는 엄격한 순서", "양의 차에서 얻는 엄격한 순서은 다음 식으로 나타납니다: 0 < b-a ⇒ a < b")
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "Hiệu dương suy ra thứ tự nghiêm ngặt",
            "Tính chất «Hiệu dương suy ra thứ tự nghiêm ngặt» được biểu diễn bởi: 0 < b-a ⇒ a < b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl PosDifferenceFromLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "Strict order gives a positive difference",
            "Positive difference follows from <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "严格大小关系推出差为正",
            "由 < 得到正差",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("PosDifferenceFromLess", "嚴格大小關係推出差為正", "< 推出差正")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "Ordre strict et différence positive",
            "Une différence positive découle de <",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "Строгий порядок даёт положительную разность",
            "Положительная разность следует из <",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "Orden estricto da una diferencia positiva",
            "Una diferencia positiva se deduce de <",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "الترتيب الصارم يعطي فرقًا موجبًا",
            "ينتج الفرق الموجب من <",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "厳密な大小関係による差の正値性",
            "< から差の正値性を導きます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "엄격한 순서에 따른 차의 양수성",
            "<로 차의 양수성을 도출합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "Thứ tự nghiêm ngặt cho hiệu dương",
            "Hiệu dương suy ra từ <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl ModRemainderStrictUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "mod remainder < |mod|",
            "Euclidean remainder is strictly less than the modulus",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "模余数 < |模|",
            "欧几里得余数严格小于模",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "模餘數 < |模數|",
            "Euclid 餘數嚴格小於模數",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "Reste modulaire < |module|",
            "Le reste euclidien est strictement inférieur au module",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "Остаток < |модуль|",
            "Евклидов остаток строго меньше модуля",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "Resto modular < |módulo|",
            "El resto euclídeo es estrictamente menor que el módulo",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "باقي القسمة < |المقياس|",
            "الباقي الإقليدي أصغر تمامًا من المقياس",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "剰余 < |法|",
            "ユークリッドの剰余は法より厳密に小さいです",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "나머지 < |법|",
            "유클리드 나머지는 법보다 엄격히 작습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "Số dư < |môđun|",
            "Số dư Euclid nhỏ hơn môđun nghiêm ngặt",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl DivMonotoneStrictSamePosDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "÷ monotone strict (pos)",
            "Division by the same positive divisor preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "除法严格单调（正）",
            "同除以正除数保持严格序",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "正除數嚴格序單調性",
            "同除正數保持嚴格序",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "Monotonie stricte avec diviseur positif",
            "Diviser par le même diviseur positif préserve l’ordre strict",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "Строгая монотонность с положительным делителем",
            "Деление на один положительный делитель сохраняет строгий порядок",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "Monotonía estricta con divisor positivo",
            "Dividir por el mismo divisor positivo conserva el orden estricto",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "رتابة صارمة بمقسوم عليه موجب",
            "القسمة على المقسوم عليه الموجب نفسه تحفظ الترتيب الصارم",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "正の除数の狭義単調性",
            "同じ正の数で割ると狭義順序を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "양수 제수의 엄격한 단조성",
            "같은 양수로 나누면 엄격한 순서가 보존됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "Đơn điệu nghiêm ngặt với số chia dương",
            "Chia cùng số chia dương bảo toàn thứ tự nghiêm ngặt",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl DivByGtOneLessSelfBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "÷(>1) < self",
            "Dividing by a number greater than one yields a strictly smaller positive value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "除以大于 1 小于自身",
            "除以大于 1 的数得到严格更小的正值",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "除以大於一的數使正值變小",
            "正值除以大於一的數得嚴格較小正值",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "Division par >1 diminue un positif",
            "Diviser une valeur positive par un nombre supérieur à un donne une valeur positive strictement inférieure",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "Деление на >1 уменьшает положительное",
            "Деление положительного значения на число больше единицы даёт строго меньшее положительное значение",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "Dividir por >1 reduce un positivo",
            "Dividir un valor positivo por un número mayor que uno da un valor positivo estrictamente menor",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "القسمة على >1 تصغّر القيمة الموجبة",
            "قسمة قيمة موجبة على عدد أكبر من واحد تعطي قيمة موجبة أصغر تمامًا",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "正値を >1 で割ると小さくなる",
            "正の値を一より大きい数で割ると厳密に小さい正の値になります",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "양수를 >1로 나누면 작아짐",
            "양의 값을 1보다 큰 수로 나누면 엄격히 작은 양의 값이 됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "Chia giá trị dương cho >1 cho giá trị nhỏ hơn",
            "Chia giá trị dương cho số lớn hơn một cho giá trị dương nhỏ hơn nghiêm ngặt",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl DivMonotoneStrictSameNegDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "÷ monotone strict (neg)",
            "Division by the same negative divisor reverses and preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "除法严格单调（负）",
            "同除以负除数反转并保持严格序",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "負除數嚴格序單調性",
            "同除負數反轉並保持嚴格序",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "Monotonie stricte avec diviseur négatif",
            "Diviser par le même diviseur négatif inverse et préserve l’ordre strict",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "Строгая монотонность с отрицательным делителем",
            "Деление на один отрицательный делитель обращает и сохраняет строгий порядок",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "Monotonía estricta con divisor negativo",
            "Dividir por el mismo divisor negativo invierte y conserva el orden estricto",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "رتابة صارمة بمقسوم عليه سالب",
            "القسمة على المقسوم عليه السالب نفسه تعكس وتحفظ الترتيب الصارم",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "負の除数の狭義単調性",
            "同じ負の数で割ると順序を反転して狭義順序を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "음수 제수의 엄격한 단조성",
            "같은 음수로 나누면 순서를 반전하고 엄격한 순서를 보존합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "Đơn điệu nghiêm ngặt với số chia âm",
            "Chia cùng số chia âm đảo chiều và bảo toàn thứ tự nghiêm ngặt",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NumericLowerBoundWeakenLtBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "Weaken numeric lower (<)",
            "A numeric lower bound weakens under <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "放宽数值下界（<）",
            "数值下界在 < 下可放宽",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "放寬數值下界（<）",
            "數值下界依 < 放寬",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "Relâchement de borne inférieure (<)",
            "Une borne inférieure numérique se relâche sous <",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "Ослабление нижней границы (<)",
            "Числовая нижняя граница ослабляется по <",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "Debilitar cota inferior (<)",
            "Una cota inferior numérica se debilita bajo <",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "إضعاف الحد الأدنى (<)",
            "الحد الأدنى العددي يضعف تحت <",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "数値下界の緩和（<）",
            "数値の下界を < で緩めます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "수치 하한 완화 (<)",
            "수치 하한을 <로 완화합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "Nới cận dưới (<)",
            "Cận dưới số được nới theo <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl NumericUpperBoundWeakenLtBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "Weaken numeric upper (<)",
            "A numeric upper bound weakens under <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "放宽数值上界（<）",
            "数值上界在 < 下可放宽",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "放寬數值上界（<）",
            "數值上界依 < 放寬",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "Relâchement de borne supérieure (<)",
            "Une borne supérieure numérique se relâche sous <",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "Ослабление верхней границы (<)",
            "Числовая верхняя граница ослабляется по <",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "Debilitar cota superior (<)",
            "Una cota superior numérica se debilita bajo <",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "إضعاف الحد الأعلى (<)",
            "الحد الأعلى العددي يضعف تحت <",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "数値上界の緩和（<）",
            "数値の上界を < で緩めます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "수치 상한 완화 (<)",
            "수치 상한을 <로 완화합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "Nới cận trên (<)",
            "Cận trên số được nới theo <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl PositiveEvenGtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "Positive even > 1",
            "A positive even integer is greater than one",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PositiveEvenGtOne", "正偶数 > 1", "正偶数大于 1")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("PositiveEvenGtOne", "正偶數 > 1", "正偶整數大於一")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "Pair positif > 1",
            "Un entier pair positif est supérieur à un",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "Положительное чётное > 1",
            "Положительное чётное целое больше единицы",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "Par positivo > 1",
            "Un entero par positivo es mayor que uno",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "زوجي موجب > 1",
            "العدد الصحيح الزوجي الموجب أكبر من واحد",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "正の偶数 > 1",
            "正の偶整数は一より大きいです",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "양의 짝수 > 1",
            "양의 짝수 정수는 1보다 큽니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "Chẵn dương > 1",
            "Số nguyên chẵn dương lớn hơn một",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl AddRightCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Add right (<)",
            "Adding the same term on the right preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右边加（<）",
            "右边加上相同项保持 <",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右加法（<）",
            "右加相同項保持 <",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Addition à droite (<)",
            "Ajouter le même terme à droite préserve <",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Сложение справа (<)",
            "Добавление одного члена справа сохраняет <",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Suma derecha (<)",
            "Sumar el mismo término a la derecha conserva <",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "جمع أيمن (<)",
            "إضافة الحد نفسه يمينًا تحفظ <",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右加算（<）",
            "右に同じ項を加えても < を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "오른쪽 덧셈 (<)",
            "오른쪽에 같은 항을 더하면 <가 보존됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Cộng phải (<)",
            "Cộng cùng hạng bên phải bảo toàn <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl AddLeftCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Add left (<)",
            "Adding the same term on the left preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "左边加（<）",
            "左边加上相同项保持 <",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("AddLeftCongruenceStrict", "左加法（<）", "左加相同項保持 <")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Addition à gauche (<)",
            "Ajouter le même terme à gauche préserve <",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Сложение слева (<)",
            "Добавление одного члена слева сохраняет <",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Suma izquierda (<)",
            "Sumar el mismo término a la izquierda conserva <",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "جمع أيسر (<)",
            "إضافة الحد نفسه يسارًا تحفظ <",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "左加算（<）",
            "左に同じ項を加えても < を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "왼쪽 덧셈 (<)",
            "왼쪽에 같은 항을 더하면 <가 보존됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Cộng trái (<)",
            "Cộng cùng hạng bên trái bảo toàn <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Left multiplication by a positive factor preserves strict order",
            "Multiplying on the left by a positive factor preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左乘正数保持严格大小关系",
            "左边乘以正因子保持 <",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左乘正數保持嚴格大小關係",
            "左乘正因子保持 <",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Multiplication à gauche par un positif et ordre strict",
            "Multiplier à gauche par un facteur positif préserve <",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Умножение слева на положительное число сохраняет строгий порядок",
            "Умножение слева на положительный множитель сохраняет <",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Multiplicación izquierda por un positivo conserva el orden estricto",
            "La propiedad «Multiplicación izquierda por un positivo conserva el orden estricto» se expresa como: k > 0 ∧ a > b ⇒ k·a > k·b",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "الضرب من اليسار في موجب يحفظ الترتيب الصارم",
            "الضرب يسارًا بعامل موجب يحفظ <",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "正の数の左乗算による厳密な大小関係の保存",
            "左に正因子を掛けると < を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "양수의 왼쪽 곱셈에 따른 엄격한 순서 보존",
            "왼쪽에 양의 인자를 곱하면 <가 보존됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Nhân bên trái với số dương bảo toàn thứ tự nghiêm ngặt",
            "Nhân bên trái với thừa số dương bảo toàn <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl MulRightPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "× right monotone (<)",
            "Multiplying on the right by a positive factor preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "右乘单调（<）",
            "右边乘以正因子保持 <",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "右乘單調性（<）",
            "右乘正因子保持 <",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Monotonie de multiplication droite (<)",
            "Multiplier à droite par un facteur positif préserve <",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Монотонность умножения справа (<)",
            "Умножение справа на положительный множитель сохраняет <",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Monotonía de multiplicación derecha (<)",
            "Multiplicar a la derecha por factor positivo conserva <",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "رتابة الضرب الأيمن (<)",
            "الضرب يمينًا بعامل موجب يحفظ <",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "右乗算の単調性（<）",
            "右に正因子を掛けると < を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "오른쪽 곱셈 단조성 (<)",
            "오른쪽에 양의 인자를 곱하면 <가 보존됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Đơn điệu nhân phải (<)",
            "Nhân bên phải với thừa số dương bảo toàn <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl OrderSignFromPositiveLiteralBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "Sign from positive bound",
            "A positive literal bound forces the stated order/sign",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "由正下界得符号",
            "正的字面下界推出所述序/符号关系",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "由正數界得符號",
            "正字面值界推出所述序或符號",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "Signe depuis une borne positive",
            "Une borne littérale positive impose l'ordre ou le signe indiqué",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "Знак из положительной границы",
            "Положительная литеральная граница задаёт указанный порядок или знак",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "Signo desde cota positiva",
            "Una cota literal positiva fuerza el orden o signo indicado",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "إشارة من حد موجب",
            "حد حرفي موجب يفرض الترتيب أو الإشارة المذكورة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "正の境界から符号",
            "正のリテラルの境界から指定された順序または符号を導きます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "양수 경계로 부호",
            "양수 리터럴 경계로 명시된 순서 또는 부호를 도출합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "Dấu từ cận dương",
            "Cận literal dương suy ra thứ tự hoặc dấu đã nêu",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl OrderFlipMulMinusOneToLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "Order flip by ×(-1)",
            "Multiplying by -1 reverses the inequality",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "乘以 -1 反转不等式",
            "两边同乘 -1 后不等式方向相反",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "乘以 -1 反轉序",
            "乘以 -1 反轉不等式方向",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "Inversion d'ordre par ×(-1)",
            "Multiplier par -1 inverse l'inégalité",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "Обращение порядка при ×(-1)",
            "Умножение на -1 обращает неравенство",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "Inversión de orden por ×(-1)",
            "Multiplicar por -1 invierte la desigualdad",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "عكس الترتيب بالضرب في (-1)",
            "الضرب في -1 يعكس المتباينة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "×(-1) による順序反転",
            "-1 を掛けると不等号が反転します",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "×(-1)에 의한 순서 반전",
            "-1을 곱하면 부등호가 반전됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "Đảo thứ tự bởi ×(-1)",
            "Nhân với -1 đảo chiều bất đẳng thức",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}

impl FromKnownGreaterBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "Known converse order",
            "The opposite-direction comparison is already known",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "已知反向序关系",
            "引用已知的反向比较事实",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("FromKnownGreater", "已知反向序關係", "反方向比較已知")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "Ordre inverse connu",
            "La comparaison dans le sens opposé est déjà connue",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "Известный обратный порядок",
            "Сравнение в обратном направлении уже известно",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "Orden inverso conocido",
            "La comparación en sentido opuesto ya es conocida",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "ترتيب عكسي معلوم",
            "المقارنة في الاتجاه المعاكس معلومة بالفعل",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "既知の逆向きの順序",
            "逆向きの比較は既知です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "알려진 역방향 순서",
            "반대 방향의 비교가 이미 알려져 있습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "Thứ tự đảo chiều đã biết",
            "So sánh theo chiều ngược đã biết",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}
