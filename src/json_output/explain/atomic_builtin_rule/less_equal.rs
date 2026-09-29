//! Explain + cite for `LessEqualFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{LessEqualFactSearchProofByBuiltinRule,
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
    FiniteSetMinMemberLeBuiltinRuleProof,
    FiniteSetSizeAtLeastOneLeBuiltinRuleProof,
    FiniteSetSizeNonnegativeLeBuiltinRuleProof,
    FiniteSetSizeSubsetLeBuiltinRuleProof,
    FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof,
    FiniteSetSizeUnionLeSumBuiltinRuleProof,
    FromKnownInNaturalBuiltinRuleProof,
    FromKnownInNegativeStandardSetForLessEqualBuiltinRuleProof,
    FromKnownInPositiveNaturalBuiltinRuleProof,
    FromKnownInPositiveStandardSetForLessEqualBuiltinRuleProof,
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
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::{family_fallback, text};

impl LessEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::OrderReflexivity(p) => p.rule_id_and_message(lang),
            Self::FromKnownLess(p) => p.rule_id_and_message(lang),
            Self::FromKnownInNatural(p) => p.rule_id_and_message(lang),
            Self::FromKnownInPositiveStandardSet(p) => p.rule_id_and_message(lang),
            Self::FromKnownInNegativeStandardSet(p) => p.rule_id_and_message(lang),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::ArccosPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArccosPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::UnitCircleLowerBound(p) => p.rule_id_and_message(lang),
            Self::UnitCircleUpperBound(p) => p.rule_id_and_message(lang),
            Self::AbsNonnegative(p) => p.rule_id_and_message(lang),
            Self::AddRightNonnegative(p) => p.rule_id_and_message(lang),
            Self::AddLeftNonnegative(p) => p.rule_id_and_message(lang),
            Self::AddRightCongruence(p) => p.rule_id_and_message(lang),
            Self::AddLeftCongruence(p) => p.rule_id_and_message(lang),
            Self::SubNonnegative(p) => p.rule_id_and_message(lang),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_id_and_message(lang),
            Self::MulRightNonnegativeMonotone(p) => p.rule_id_and_message(lang),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_id_and_message(lang),
            Self::AbsLeImpliesUpper(p) => p.rule_id_and_message(lang),
            Self::AbsLeImpliesNegUpper(p) => p.rule_id_and_message(lang),
            Self::AbsSelfUpper(p) => p.rule_id_and_message(lang),
            Self::AbsSelfLower(p) => p.rule_id_and_message(lang),
            Self::AbsTriangleInequality(p) => p.rule_id_and_message(lang),
            Self::AbsReverseTriangleAdd(p) => p.rule_id_and_message(lang),
            Self::AbsReverseTriangleSub(p) => p.rule_id_and_message(lang),
            Self::SumOfNonnegatives(p) => p.rule_id_and_message(lang),
            Self::ProductOfNonnegatives(p) => p.rule_id_and_message(lang),
            Self::EvenPowNonnegative(p) => p.rule_id_and_message(lang),
            Self::PowNonnegFromPositiveBase(p) => p.rule_id_and_message(lang),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_id_and_message(lang),
            Self::SqrtNonnegative(p) => p.rule_id_and_message(lang),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_id_and_message(lang),
            Self::FromKnownInPositiveNatural(p) => p.rule_id_and_message(lang),
            Self::LogOrderPreservingWeak(p) => p.rule_id_and_message(lang),
            Self::LessEqualTransitivity(p) => p.rule_id_and_message(lang),
            Self::LessEqualFromNonnegDifference(p) => p.rule_id_and_message(lang),
            Self::NonnegDifferenceFromLessEqual(p) => p.rule_id_and_message(lang),
            Self::ModRemainderNonnegative(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_id_and_message(lang),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_id_and_message(lang),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_id_and_message(lang),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_id_and_message(lang),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_id_and_message(lang),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_id_and_message(lang),
            Self::IntegerSuccessorLe(p) => p.rule_id_and_message(lang),
            Self::IntegerAdjacencyLe(p) => p.rule_id_and_message(lang),
            Self::IntegerPredecessorLe(p) => p.rule_id_and_message(lang),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetMaxMemberLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetMinMemberLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_id_and_message(lang),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message(lang),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownLess(p) => Some(p.cite_fact_id),
            Self::FromKnownInNatural(p) => Some(p.cite_fact_id),
            Self::FromKnownInPositiveStandardSet(p) => Some(p.cite_fact_id),
            Self::FromKnownInNegativeStandardSet(p) => Some(p.cite_fact_id),
            Self::AbsLeImpliesUpper(p) => Some(p.cite_fact_id),
            Self::AbsLeImpliesNegUpper(p) => Some(p.cite_fact_id),
            Self::FromKnownInPositiveNatural(p) => Some(p.cite_fact_id),
            Self::LessEqualTransitivity(_) => None,
            Self::LessEqualFromNonnegDifference(p) => Some(p.cite_fact_id),
            Self::NonnegDifferenceFromLessEqual(p) => Some(p.cite_fact_id),
            Self::NumericLowerBoundWeakenLe(p) => Some(p.cite_fact_id),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => Some(p.cite_fact_id),
            Self::NumericUpperBoundWeakenLe(p) => Some(p.cite_fact_id),
            Self::OrderFlipMulMinusOne(p) => Some(p.cite_fact_id),
            Self::OrderSignFromNegativeLiteralBound(p) => Some(p.cite_fact_id),
            _ => None,
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl OrderReflexivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderReflexivity",
            "Order reflexivity",
            "A quantity is less-or-equal to itself",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderReflexivity",
            "序的自反性",
            "任何量都不大于也不小于自己（≤ 自身）",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "From known less",
            "The weak order follows from a known strict less fact",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "已知严格小于",
            "弱序目标由已知的严格小于推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownInNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownInNatural",
            "From known in N",
            "The goal follows from a known natural-number membership",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownInNatural",
            "已知属于自然数",
            "目标由已知的自然数成员关系推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownInPositiveStandardSetForLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownInPositiveStandardSet",
            "From known in positive set",
            "The goal follows from membership in a positive standard set",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownInPositiveStandardSet",
            "已知属于正标准集",
            "目标由正标准集上的成员关系推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownInNegativeStandardSetForLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownInNegativeStandardSet",
            "From known in negative set",
            "The goal follows from membership in a negative standard set",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownInNegativeStandardSet",
            "已知属于负标准集",
            "目标由负标准集上的成员关系推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ArcsinPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArcsinPrincipalLowerBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ArcsinPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArcsinPrincipalUpperBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ArccosPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArccosPrincipalLowerBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ArccosPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArccosPrincipalUpperBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl UnitCircleLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("UnitCircleLowerBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl UnitCircleUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("UnitCircleUpperBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsNonnegative", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AddRightNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AddRightNonnegative", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AddLeftNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AddLeftNonnegative", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AddRightCongruenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AddRightCongruence", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AddLeftCongruenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AddLeftCongruence", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SubNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SubNonnegative", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl MulLeftNonnegativeMonotoneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("MulLeftNonnegativeMonotone", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl MulRightNonnegativeMonotoneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("MulRightNonnegativeMonotone", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsLeFromSymmetricBoundsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsLeFromSymmetricBounds", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsLeImpliesUpperBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsLeImpliesUpper", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsLeImpliesNegUpperBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsLeImpliesNegUpper", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsSelfUpperBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsSelfUpper", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsSelfLowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsSelfLower", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsTriangleInequalityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsTriangleInequality", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsReverseTriangleAddBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsReverseTriangleAdd", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl AbsReverseTriangleSubBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AbsReverseTriangleSub", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SumOfNonnegativesBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SumOfNonnegatives", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ProductOfNonnegativesBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ProductOfNonnegatives", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl EvenPowNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("EvenPowNonnegative", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl PowNonnegFromPositiveBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("PowNonnegFromPositiveBase", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("PowNonnegFromNonnegBasePosIntExp", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SqrtNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SqrtNonnegative", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SqrtMonotoneNondecreasingBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SqrtMonotoneNondecreasing", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownInPositiveNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownInPositiveNatural",
            "From known in positive N",
            "The goal follows from a known positive-natural membership",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownInPositiveNatural",
            "已知属于正自然数",
            "目标由已知的正自然数成员关系推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LogOrderPreservingWeakBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LogOrderPreservingWeak", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LessEqualTransitivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LessEqualTransitivity", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LessEqualFromNonnegDifferenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LessEqualFromNonnegDifference", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NonnegDifferenceFromLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("NonnegDifferenceFromLessEqual", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl ModRemainderNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ModRemainderNonnegative", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl DivMonotoneWeakSamePosDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("DivMonotoneWeakSamePosDivisor", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSizeNonnegativeLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FiniteSetSizeNonnegativeLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSizeAtLeastOneLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FiniteSetSizeAtLeastOneLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSizeSubsetLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FiniteSetSizeSubsetLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl DivMonotoneWeakSameNegDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("DivMonotoneWeakSameNegDivisor", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LessEqualFromPosDivProductBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LessEqualFromPosDivProductBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LessEqualFromPosDenomQuotientBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LessEqualFromPosDenomQuotientBound", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NumericLowerBoundWeakenLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("NumericLowerBoundWeakenLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("NumericLowerBoundFromStrictPredecessorLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NumericUpperBoundWeakenLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("NumericUpperBoundWeakenLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl IntegerSuccessorLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("IntegerSuccessorLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl IntegerAdjacencyLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("IntegerAdjacencyLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl IntegerPredecessorLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("IntegerPredecessorLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl IntegerDiffAtLeastOneLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("IntegerDiffAtLeastOneLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetMaxMemberLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FiniteSetMaxMemberLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetMinMemberLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FiniteSetMinMemberLe", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSizeUnionLeSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FiniteSetSizeUnionLeSum", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("FiniteSetSizeSurjectionCodomainLeDomain", OutputLanguage::English)
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        self.rule_id_and_message_en()
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}


impl OrderFlipMulMinusOneToLessEqualBuiltinRuleProof {
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl OrderSignFromNegativeLiteralBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromNegativeLiteralBound",
            "Sign from negative bound",
            "A negative literal bound forces the stated order/sign",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromNegativeLiteralBound",
            "由负上界得符号",
            "负的字面上界推出所述序/符号关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}
