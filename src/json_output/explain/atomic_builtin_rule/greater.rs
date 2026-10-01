//! Leaf explain for atomic family group `greater`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater::{
    AddLeftCongruenceStrictBuiltinRuleProof,
    AddRightCongruenceStrictBuiltinRuleProof,
    ClosedNumericComparisonBuiltinRuleProof,
    FromKnownLessBuiltinRuleProof,
    FromPositiveRealMembershipBuiltinRuleProof,
    GreaterFactSearchProofByBuiltinRule,
    MulLeftPositiveMonotoneStrictBuiltinRuleProof,
    MulRightPositiveMonotoneStrictBuiltinRuleProof,
    NativeEulerGreaterZeroBuiltinRuleProof,
    NativePiGreaterZeroBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl GreaterFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::FromKnownLess(p) => p.rule_id_and_message(lang),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message(lang),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message(lang),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::ClosedNumericComparison(_) => None,
            Self::FromKnownLess(p) => p.premise_proof.cite_fact_id(),
            Self::AddRightCongruenceStrict(_) => None,
            Self::AddLeftCongruenceStrict(_) => None,
            Self::MulLeftPositiveMonotoneStrict(_) => None,
            Self::MulRightPositiveMonotoneStrict(_) => None,
            Self::FromPositiveRealMembership(_) => None,
            Self::NativeEulerGreaterZero(_) => None,
            Self::NativePiGreaterZero(_) => None,
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Closed Numeric Comparison",
            "if both sides evaluate to decimals L, R with L > R,",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "封闭数值比较",
            "两边算出的数满足目标比较关系",
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
            "From Known Less",
            "`>` is the converse of `<`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "已知严格小于",
            "目标由已知的严格小于事实推出",
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
            "Add Right Congruence Strict",
            "Right addend congruence (strict): `a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右边加法同余（严格）",
            "严格序在右边加同一项后保持",
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
            "Add Left Congruence Strict",
            "Left addend congruence (strict): `a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "左边加法同余（严格）",
            "严格序在左边加同一项后保持",
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
            "Mul Left Positive Monotone Strict",
            "`0 < k` and `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左边正数乘法保序（严格）",
            "正因子左边乘法保持严格序",
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
            "Mul Right Positive Monotone Strict",
            "Right multiplication by a positive factor preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "右边正数乘法保序（严格）",
            "正因子右边乘法保持严格序",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FromPositiveRealMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "From Positive Real Membership",
            "`x $in R+` ⇒ `x > 0`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "由正实数成员推出",
            "正实数成员蕴含严格大于零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NativeEulerGreaterZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "Native Euler Greater Zero",
            "Native Euler constant is strictly positive: `e > 0`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "自然常数 e 大于零",
            "自然常数 e 严格大于零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl NativePiGreaterZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "Native Pi Greater Zero",
            "Native Pi constant is strictly positive: `pi > 0`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "圆周率 π 大于零",
            "圆周率 π 严格大于零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

