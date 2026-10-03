//! GreaterEqual (`a >= b`) builtin explain + cite.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::{
    FromKnownLessEqualBuiltinRuleProof,

    ClosedNumericComparisonBuiltinRuleProof, FiniteSetSizeAtLeastOneBuiltinRuleProof,
    FiniteSetSizeNonnegativeBuiltinRuleProof, FromKnownGreaterBuiltinRuleProof,
    FromKnownInPositiveNaturalBuiltinRuleProof,
    GreaterEqualFactSearchProofByBuiltinRule, OrderReflexivityBuiltinRuleProof,
    PredecessorNonNegFromAtLeastOneBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;

use super::text::text;

impl GreaterEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ComplexModulusNonnegative => match lang {
                OutputLanguage::English => text("ComplexModulusNonnegative", "Nonnegative complex modulus", "The principal complex modulus is nonnegative"),
                OutputLanguage::Chinese => text("ComplexModulusNonnegative", "复数模长非负", "复数模长取非负主根"),
            },
            Self::FromKnownLessEqual(p) => p.rule_id_and_message(lang),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message(lang),
            Self::FromKnownInPositiveNatural(p) => p.rule_id_and_message(lang),
            Self::FromKnownGreater(p) => p.rule_id_and_message(lang),
            Self::OrderReflexivity(p) => p.rule_id_and_message(lang),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message(lang),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeNonnegative(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownLessEqual(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownInPositiveNatural(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownGreater(p) => p.premise_proof.cite_fact_id(),
            Self::OrderFlipMulMinusOne(p) => p.premise_proof.cite_fact_id(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.at_least_one_proof.cite_fact_id(),
            Self::OrderReflexivity(_)
            | Self::ClosedNumericComparison(_)
            | Self::FiniteSetSizeNonnegative(_)
            | Self::FiniteSetSizeAtLeastOne(_) => None,
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

impl FromKnownGreaterBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "From known greater",
            "The weak order follows from a known strict greater fact",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownGreater",
            "已知严格大于",
            "弱序目标由已知的严格大于推出",
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

impl PredecessorNonNegFromAtLeastOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PredecessorNonNegFromAtLeastOne",
            "n-1 ≥ 0 from n ≥ 1",
            "Predecessor is nonnegative when the value is at least one",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PredecessorNonNegFromAtLeastOne",
            "由 n ≥ 1 得 n-1 ≥ 0",
            "当值至少为 1 时前驱非负",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSizeNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeNonnegative",
            "|S| ≥ 0",
            "Finite-set size is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeNonnegative",
            "|S| ≥ 0",
            "有限集大小非负",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl FiniteSetSizeAtLeastOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeAtLeastOne",
            "|S| ≥ 1",
            "A nonempty finite set has size at least one",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeAtLeastOne",
            "|S| ≥ 1",
            "非空有限集大小至少为 1",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof {
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

impl FromKnownLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("FromKnownLessEqual", "Known converse order", "The opposite-direction comparison is already known"),
            OutputLanguage::Chinese => text("FromKnownLessEqual", "已知反向序关系", "引用已知的反向比较事实"),
        }
    }
}
