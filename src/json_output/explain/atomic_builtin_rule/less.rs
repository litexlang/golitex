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
    SqrtPositiveBuiltinRuleProof, SubtractOneLessBuiltinRuleProof, SumBothPositiveBuiltinRuleProof,
    SumLeftNonnegativeRightStrictBuiltinRuleProof, SumLeftStrictRightNonnegativeBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromPositiveLiteralBoundBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl LessFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message(lang),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message(lang),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::SubtractOneLess(p) => p.rule_id_and_message(lang),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::SumBothPositive(p) => p.rule_id_and_message(lang),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message(lang),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message(lang),
            Self::ProductBothPositive(p) => p.rule_id_and_message(lang),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message(lang),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message(lang),
            Self::SqrtPositive(p) => p.rule_id_and_message(lang),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message(lang),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message(lang),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message(lang),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message(lang),
            Self::LessTransitivity(p) => p.rule_id_and_message(lang),
            Self::LessFromPosDifference(p) => p.rule_id_and_message(lang),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message(lang),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message(lang),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message(lang),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message(lang),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message(lang),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message(lang),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message(lang),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message(lang),
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
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FiniteSetSizeProperSubsetLt",
                "Proper finite subset cardinality",
                "A proper subset of a finite set has strictly smaller cardinality",
            ),
            OutputLanguage::Chinese => text(
                "FiniteSetSizeProperSubsetLt",
                "有限真子集的基数严格更小",
                "有限集合的真子集具有严格更小的基数",
            ),
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

impl SubtractOneLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "n-1 < n",
            "Subtracting one yields a strictly smaller value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "n-1 < n",
            "减一得到严格更小的值",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "SumBothPositive",
            "正数和 > 0",
            "正项之和为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "ProductBothPositive",
            "正数积 > 0",
            "正因子之积为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl EvenPowPositiveFromNonzeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "Even power > 0",
            "An even power of a nonzero value is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "偶次幂 > 0",
            "非零数的偶次幂为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SqrtPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "√ > 0",
            "Square root of a positive value is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "√ > 0",
            "正数的平方根为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LogPositiveFromBaseAndArgGtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "log > 0 when arg > 1",
            "Log with base > 1 is positive when the argument is > 1",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "真数 > 1 时对数 > 0",
            "底大于 1 且真数大于 1 时对数为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "log < 0 on (0,1)",
            "Log with base > 1 is negative on (0,1)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "对数在 (0,1) 上 < 0",
            "底大于 1 时对数在 (0,1) 上为负",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "LessTransitivity",
            "< 传递性",
            "< 具有传递性",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LessFromPosDifferenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "< from positive difference",
            "a < b when b-a is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "由正差得 <",
            "当 b-a 为正时 a < b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl PosDifferenceFromLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "b-a > 0 from a < b",
            "Positive difference follows from <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "由 a < b 得 b-a > 0",
            "由 < 得到正差",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "PositiveEvenGtOne",
            "正偶数 > 1",
            "正偶数大于 1",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "× left monotone (<)",
            "Multiplying on the left by a positive factor preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左乘单调（<）",
            "左边乘以正因子保持 <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromKnownGreaterBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("FromKnownGreater", "Known converse order", "The opposite-direction comparison is already known"),
            OutputLanguage::Chinese => text("FromKnownGreater", "已知反向序关系", "引用已知的反向比较事实"),
        }
    }
}
