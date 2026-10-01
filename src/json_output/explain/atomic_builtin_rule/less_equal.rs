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
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl LessEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::OrderReflexivity(p) => p.rule_id_and_message(lang),
            Self::FromKnownLess(p) => p.rule_id_and_message(lang),
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
            Self::FromKnownLess(p) => p.premise_proof.cite_fact_id(),
            Self::AbsLeImpliesUpper(p) => p.premise_proof.cite_fact_id(),
            Self::AbsLeImpliesNegUpper(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownInPositiveNatural(p) => p.premise_proof.cite_fact_id(),
            Self::LessEqualTransitivity(_) => None,
            Self::LessEqualFromNonnegDifference(p) => p.premise_proof.cite_fact_id(),
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




impl ArcsinPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArcsinPrincipalLowerBound",
            "arcsin lower bound",
            "arcsin stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArcsinPrincipalLowerBound",
            "arcsin 下界",
            "arcsin 落在其主值下界内",
        )
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
        text(
            "ArcsinPrincipalUpperBound",
            "arcsin upper bound",
            "arcsin stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArcsinPrincipalUpperBound",
            "arcsin 上界",
            "arcsin 落在其主值上界内",
        )
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
        text(
            "ArccosPrincipalLowerBound",
            "arccos lower bound",
            "arccos stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccosPrincipalLowerBound",
            "arccos 下界",
            "arccos 落在其主值下界内",
        )
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
        text(
            "ArccosPrincipalUpperBound",
            "arccos upper bound",
            "arccos stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccosPrincipalUpperBound",
            "arccos 上界",
            "arccos 落在其主值上界内",
        )
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
        text(
            "UnitCircleLowerBound",
            "Unit-circle lower bound",
            "Trig values on the unit circle respect the lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnitCircleLowerBound",
            "单位圆下界",
            "单位圆上的三角函数值满足下界",
        )
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
        text(
            "UnitCircleUpperBound",
            "Unit-circle upper bound",
            "Trig values on the unit circle respect the upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnitCircleUpperBound",
            "单位圆上界",
            "单位圆上的三角函数值满足上界",
        )
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
        text(
            "AbsNonnegative",
            "|x| ≥ 0",
            "Absolute value is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsNonnegative",
            "|x| ≥ 0",
            "绝对值非负",
        )
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
        text(
            "AddRightNonnegative",
            "Add right nonnegative",
            "Adding a nonnegative term on the right preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddRightNonnegative",
            "右边加非负",
            "右边加上非负项保持 ≤",
        )
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
        text(
            "AddLeftNonnegative",
            "Add left nonnegative",
            "Adding a nonnegative term on the left preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddLeftNonnegative",
            "左边加非负",
            "左边加上非负项保持 ≤",
        )
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
        text(
            "AddRightCongruence",
            "Add right (≤)",
            "Adding the same term on the right preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruence",
            "右边加（≤）",
            "右边加上相同项保持 ≤",
        )
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
        text(
            "AddLeftCongruence",
            "Add left (≤)",
            "Adding the same term on the left preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruence",
            "左边加（≤）",
            "左边加上相同项保持 ≤",
        )
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
        text(
            "SubNonnegative",
            "a-b ≥ 0",
            "A difference is nonnegative under the stated premises",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SubNonnegative",
            "a-b ≥ 0",
            "在所述前提下差非负",
        )
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
        text(
            "MulLeftNonnegativeMonotone",
            "× left monotone (≤)",
            "Multiplying on the left by a nonnegative factor preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftNonnegativeMonotone",
            "左乘单调（≤）",
            "左边乘以非负因子保持 ≤",
        )
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
        text(
            "MulRightNonnegativeMonotone",
            "× right monotone (≤)",
            "Multiplying on the right by a nonnegative factor preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulRightNonnegativeMonotone",
            "右乘单调（≤）",
            "右边乘以非负因子保持 ≤",
        )
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
        text(
            "AbsLeFromSymmetricBounds",
            "|x| ≤ M from ± bounds",
            "Absolute value is bounded by M when -M ≤ x ≤ M",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsLeFromSymmetricBounds",
            "由 ± 界得 |x| ≤ M",
            "当 -M ≤ x ≤ M 时，|x| ≤ M",
        )
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
        text(
            "AbsLeImpliesUpper",
            "|x| ≤ M ⇒ x ≤ M",
            "An absolute-value upper bound implies the same bound on x",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsLeImpliesUpper",
            "|x| ≤ M ⇒ x ≤ M",
            "绝对值上界蕴含 x 的同样上界",
        )
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
        text(
            "AbsLeImpliesNegUpper",
            "|x| ≤ M ⇒ -x ≤ M",
            "An absolute-value upper bound implies the same bound on -x",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsLeImpliesNegUpper",
            "|x| ≤ M ⇒ -x ≤ M",
            "绝对值上界蕴含 -x 的同样上界",
        )
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
        text(
            "AbsSelfUpper",
            "x ≤ |x|",
            "A quantity is at most its absolute value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsSelfUpper",
            "x ≤ |x|",
            "任何量都不大于其绝对值",
        )
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
        text(
            "AbsSelfLower",
            "-|x| ≤ x",
            "A quantity is at least the negation of its absolute value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsSelfLower",
            "-|x| ≤ x",
            "任何量都不小于其绝对值的相反数",
        )
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
        text(
            "AbsTriangleInequality",
            "Triangle inequality",
            "|a+b| ≤ |a|+|b|",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsTriangleInequality",
            "三角不等式",
            "|a+b| ≤ |a|+|b|",
        )
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
        text(
            "AbsReverseTriangleAdd",
            "Reverse triangle (|a|+|b|)",
            "Reverse triangle inequality for absolute values of a sum",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsReverseTriangleAdd",
            "反向三角（|a|+|b|）",
            "和的绝对值的反向三角不等式",
        )
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
        text(
            "AbsReverseTriangleSub",
            "Reverse triangle (|a|-|b|)",
            "Reverse triangle inequality for absolute values of a difference",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsReverseTriangleSub",
            "反向三角（|a|-|b|）",
            "差的绝对值的反向三角不等式",
        )
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
        text(
            "SumOfNonnegatives",
            "Sum of nonnegatives ≥ 0",
            "A sum of nonnegative terms is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SumOfNonnegatives",
            "非负和 ≥ 0",
            "非负项之和非负",
        )
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
        text(
            "ProductOfNonnegatives",
            "Product of nonnegatives ≥ 0",
            "A product of nonnegative factors is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ProductOfNonnegatives",
            "非负积 ≥ 0",
            "非负因子之积非负",
        )
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
        text(
            "EvenPowNonnegative",
            "Even power ≥ 0",
            "An even power is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EvenPowNonnegative",
            "偶次幂 ≥ 0",
            "偶次幂非负",
        )
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
        text(
            "PowNonnegFromPositiveBase",
            "pow ≥ 0 (pos base)",
            "A positive base raised to a real power is nonnegative where defined",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowNonnegFromPositiveBase",
            "幂 ≥ 0（正底）",
            "正底数的实数次幂在有定义时非负",
        )
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
        text(
            "PowNonnegFromNonnegBasePosIntExp",
            "pow ≥ 0 (nonneg base)",
            "A nonnegative base to a positive integer power is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowNonnegFromNonnegBasePosIntExp",
            "幂 ≥ 0（非负底）",
            "非负底数的正整数次幂非负",
        )
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
        text(
            "SqrtNonnegative",
            "√ ≥ 0",
            "Square root is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtNonnegative",
            "√ ≥ 0",
            "平方根非负",
        )
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
        text(
            "SqrtMonotoneNondecreasing",
            "√ monotone weak",
            "Square root is nondecreasing on [0,∞)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneNondecreasing",
            "√ 弱单调",
            "平方根在 [0,∞) 上非减",
        )
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
        text(
            "LogOrderPreservingWeak",
            "log order weak",
            "Log with base > 1 preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingWeak",
            "对数弱保序",
            "底大于 1 的对数保持 ≤",
        )
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
        text(
            "LessEqualTransitivity",
            "≤ transitivity",
            "Less-or-equal is transitive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessEqualTransitivity",
            "≤ 传递性",
            "≤ 具有传递性",
        )
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
        text(
            "LessEqualFromNonnegDifference",
            "≤ from nonnegative difference",
            "a ≤ b when b-a is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromNonnegDifference",
            "由非负差得 ≤",
            "当 b-a 非负时 a ≤ b",
        )
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
        text(
            "NonnegDifferenceFromLessEqual",
            "b-a ≥ 0 from a ≤ b",
            "Nonnegative difference follows from ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonnegDifferenceFromLessEqual",
            "由 a ≤ b 得 b-a ≥ 0",
            "由 ≤ 得到非负差",
        )
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
        text(
            "ModRemainderNonnegative",
            "mod remainder ≥ 0",
            "Euclidean remainder is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ModRemainderNonnegative",
            "模余数 ≥ 0",
            "欧几里得余数非负",
        )
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
        text(
            "DivMonotoneWeakSamePosDivisor",
            "÷ monotone weak (pos)",
            "Division by the same positive divisor preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneWeakSamePosDivisor",
            "除法弱单调（正）",
            "同除以正除数保持 ≤",
        )
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
        text(
            "FiniteSetSizeNonnegativeLe",
            "|S| ≥ 0 as ≤",
            "Finite-set size is nonnegative (as ≤)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeNonnegativeLe",
            "|S| ≥ 0（≤）",
            "有限集大小非负（写成 ≤）",
        )
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
        text(
            "FiniteSetSizeAtLeastOneLe",
            "|S| ≥ 1 as ≤",
            "A nonempty finite set has size at least one (as ≤)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeAtLeastOneLe",
            "|S| ≥ 1（≤）",
            "非空有限集大小至少为 1（写成 ≤）",
        )
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
        text(
            "FiniteSetSizeSubsetLe",
            "|A| ≤ |B| from A⊆B",
            "Subset relation implies a weak inequality on finite-set sizes",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSubsetLe",
            "由 A⊆B 得 |A| ≤ |B|",
            "子集关系蕴含有限集大小的弱不等式",
        )
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
        text(
            "DivMonotoneWeakSameNegDivisor",
            "÷ monotone weak (neg)",
            "Division by the same negative divisor reverses and preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneWeakSameNegDivisor",
            "除法弱单调（负）",
            "同除以负除数反转并保持 ≤",
        )
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
        text(
            "LessEqualFromPosDivProductBound",
            "≤ from positive divisor product",
            "A product bound with positive divisor yields ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromPosDivProductBound",
            "由正除数积得 ≤",
            "正除数的积界给出 ≤",
        )
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
        text(
            "LessEqualFromPosDenomQuotientBound",
            "≤ from positive-denom quotient",
            "A quotient bound with positive denominator yields ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromPosDenomQuotientBound",
            "由正分母商得 ≤",
            "正分母的商界给出 ≤",
        )
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
        text(
            "NumericLowerBoundWeakenLe",
            "Weaken numeric lower (≤)",
            "A numeric lower bound weakens under ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLe",
            "放宽数值下界（≤）",
            "数值下界在 ≤ 下可放宽",
        )
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
        text(
            "NumericLowerBoundFromStrictPredecessorLe",
            "Lower bound via predecessor",
            "A numeric lower bound follows from a strict predecessor comparison",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundFromStrictPredecessorLe",
            "由前驱得下界",
            "由严格前驱比较得到数值下界",
        )
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
        text(
            "NumericUpperBoundWeakenLe",
            "Weaken numeric upper (≤)",
            "A numeric upper bound weakens under ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLe",
            "放宽数值上界（≤）",
            "数值上界在 ≤ 下可放宽",
        )
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
        text(
            "IntegerSuccessorLe",
            "n ≤ n+1",
            "An integer is ≤ its successor",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntegerSuccessorLe",
            "n ≤ n+1",
            "整数 ≤ 其后继",
        )
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
        text(
            "IntegerAdjacencyLe",
            "Integer adjacency ≤",
            "Adjacent integers compare by ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntegerAdjacencyLe",
            "整数相邻 ≤",
            "相邻整数按 ≤ 比较",
        )
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
        text(
            "IntegerPredecessorLe",
            "n-1 ≤ n",
            "An integer predecessor is ≤ the integer",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntegerPredecessorLe",
            "n-1 ≤ n",
            "整数前驱 ≤ 该整数",
        )
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
        text(
            "IntegerDiffAtLeastOneLe",
            "Integer gap ≥ 1",
            "Distinct integers differ by at least one",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntegerDiffAtLeastOneLe",
            "整数间隔 ≥ 1",
            "不同整数至少相差 1",
        )
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
        text(
            "FiniteSetMaxMemberLe",
            "max member ≤",
            "Every member of a finite set is ≤ its maximum",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetMaxMemberLe",
            "元素 ≤ 最大值",
            "有限集每个元素 ≤ 其最大值",
        )
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
        text(
            "FiniteSetMinMemberLe",
            "min ≤ member",
            "The minimum of a finite set is ≤ every member",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetMinMemberLe",
            "最小值 ≤ 元素",
            "有限集最小值 ≤ 每个元素",
        )
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
        text(
            "FiniteSetSizeUnionLeSum",
            "|A∪B| ≤ |A|+|B|",
            "Finite-set union size is at most the sum of sizes",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeUnionLeSum",
            "|A∪B| ≤ |A|+|B|",
            "有限并集大小不超过各大小之和",
        )
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
        text(
            "FiniteSetSizeSurjectionCodomainLeDomain",
            "|codomain| ≤ |domain|",
            "A surjection implies the codomain is no larger than the domain",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSurjectionCodomainLeDomain",
            "|值域| ≤ |定义域|",
            "满射蕴含值域不大于定义域",
        )
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
