//! Leaf explain for atomic family group `not_is_finite_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_is_finite_set::{
    NotIsFiniteSetFactSearchProofByBuiltinRule,
    SetMinusInfiniteOfInfiniteFiniteBuiltinRuleProof,
    StandardInfiniteSetBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotIsFiniteSetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::StandardInfiniteSet(p) => p.rule_id_and_message(lang),
            Self::SetMinusInfiniteOfInfiniteFinite(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::StandardInfiniteSet(_) => None,
            Self::SetMinusInfiniteOfInfiniteFinite(_) => None,
        }
    }
}

impl StandardInfiniteSetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardInfiniteSet",
            "Standard Infinite Set",
            "every standard number set (N, Z, Q, R, C, and signed/star variants)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StandardInfiniteSet",
            "标准无穷集",
            "标准数集载体无穷",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl SetMinusInfiniteOfInfiniteFiniteBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusInfiniteOfInfiniteFinite",
            "Set Minus Infinite Of Infinite Finite",
            "if `A` is infinite and `B` is finite, then `set_minus(A, B)` is infinite",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusInfiniteOfInfiniteFinite",
            "无穷减有限仍无穷",
            "无穷集减去有限集仍无穷",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

