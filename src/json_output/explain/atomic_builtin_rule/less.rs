//! Explain + cite for `LessFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{
    LessFactSearchProofByBuiltinRule, AddLeftCongruenceStrictBuiltinRuleProof,
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
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::from_known_in_signed_standard_set::{
    FromKnownInNegativeStandardSetBuiltinRuleProof, FromKnownInPositiveStandardSetBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromPositiveLiteralBoundBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::{family_fallback, text};

impl LessFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
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
            Self::FromKnownInPositiveStandardSet(p) => p.rule_id_and_message(lang),
            Self::FromKnownInNegativeStandardSet(p) => p.rule_id_and_message(lang),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message(lang),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::LessTransitivity(_) => None,
            Self::LessFromPosDifference(p) => Some(p.cite_fact_id),
            Self::PosDifferenceFromLess(p) => Some(p.cite_fact_id),
            Self::NumericLowerBoundWeakenLt(p) => Some(p.cite_fact_id),
            Self::NumericUpperBoundWeakenLt(p) => Some(p.cite_fact_id),
            Self::FromKnownInPositiveStandardSet(p) => Some(p.cite_fact_id),
            Self::FromKnownInNegativeStandardSet(p) => Some(p.cite_fact_id),
            Self::OrderSignFromPositiveLiteralBound(p) => Some(p.cite_fact_id),
            Self::OrderFlipMulMinusOne(p) => Some(p.cite_fact_id),
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

impl SubtractOneLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SubtractOneLess", OutputLanguage::English)
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

impl ArctanPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArctanPrincipalLowerBound", OutputLanguage::English)
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

impl ArctanPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArctanPrincipalUpperBound", OutputLanguage::English)
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

impl ArccotPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArccotPrincipalLowerBound", OutputLanguage::English)
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

impl ArccotPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ArccotPrincipalUpperBound", OutputLanguage::English)
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

impl SumBothPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SumBothPositive", OutputLanguage::English)
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

impl SumLeftStrictRightNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SumLeftStrictRightNonnegative", OutputLanguage::English)
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

impl SumLeftNonnegativeRightStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SumLeftNonnegativeRightStrict", OutputLanguage::English)
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

impl ProductBothPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ProductBothPositive", OutputLanguage::English)
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

impl EvenPowPositiveFromNonzeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("EvenPowPositiveFromNonzero", OutputLanguage::English)
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

impl PowPositiveFromPositiveBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("PowPositiveFromPositiveBase", OutputLanguage::English)
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

impl SqrtPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SqrtPositive", OutputLanguage::English)
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

impl SqrtMonotoneIncreasingBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("SqrtMonotoneIncreasing", OutputLanguage::English)
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

impl LogOrderPreservingStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LogOrderPreservingStrict", OutputLanguage::English)
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

impl LogPositiveFromBaseAndArgGtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LogPositiveFromBaseAndArgGtOne", OutputLanguage::English)
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

impl LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LogNegativeFromBaseGtOneArgInUnitInterval", OutputLanguage::English)
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

impl LessTransitivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LessTransitivity", OutputLanguage::English)
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

impl LessFromPosDifferenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("LessFromPosDifference", OutputLanguage::English)
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

impl PosDifferenceFromLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("PosDifferenceFromLess", OutputLanguage::English)
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

impl ModRemainderStrictUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("ModRemainderStrictUpperBound", OutputLanguage::English)
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

impl DivMonotoneStrictSamePosDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("DivMonotoneStrictSamePosDivisor", OutputLanguage::English)
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

impl DivByGtOneLessSelfBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("DivByGtOneLessSelf", OutputLanguage::English)
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

impl DivMonotoneStrictSameNegDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("DivMonotoneStrictSameNegDivisor", OutputLanguage::English)
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

impl NumericLowerBoundWeakenLtBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("NumericLowerBoundWeakenLt", OutputLanguage::English)
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

impl NumericUpperBoundWeakenLtBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("NumericUpperBoundWeakenLt", OutputLanguage::English)
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

impl PositiveEvenGtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("PositiveEvenGtOne", OutputLanguage::English)
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

impl AddRightCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AddRightCongruenceStrict", OutputLanguage::English)
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

impl AddLeftCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("AddLeftCongruenceStrict", OutputLanguage::English)
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

impl MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("MulLeftPositiveMonotoneStrict", OutputLanguage::English)
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

impl MulRightPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        family_fallback("MulRightPositiveMonotoneStrict", OutputLanguage::English)
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

impl FromKnownInPositiveStandardSetBuiltinRuleProof {
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

impl FromKnownInNegativeStandardSetBuiltinRuleProof {
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

