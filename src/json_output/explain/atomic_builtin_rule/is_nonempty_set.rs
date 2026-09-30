//! Leaf explain for atomic family group `is_nonempty_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_nonempty_set::{
    IsNonemptySetFactSearchProofByBuiltinRule,
    LiteralListSetNonemptyBuiltinRuleProof,
    OneSideInfinityIntervalNonemptyBuiltinRuleProof,
    PowerSetNonemptyBuiltinRuleProof,
    StandardSetNonemptyBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl IsNonemptySetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::StandardSetNonempty(p) => p.rule_id_and_message(lang),
            Self::LiteralListSetNonempty(p) => p.rule_id_and_message(lang),
            Self::PowerSetNonempty(p) => p.rule_id_and_message(lang),
            Self::OneSideInfinityIntervalNonempty(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::StandardSetNonempty(_) => None,
            Self::LiteralListSetNonempty(_) => None,
            Self::PowerSetNonempty(_) => None,
            Self::OneSideInfinityIntervalNonempty(_) => None,
        }
    }
}

impl StandardSetNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardSetNonempty",
            "Standard Set Nonempty",
            "Verified by the standard Set Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StandardSetNonempty",
            "标准集非空",
            "标准数集非空",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl LiteralListSetNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LiteralListSetNonempty",
            "Literal List Set Nonempty",
            "Verified by the literal List Set Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LiteralListSetNonempty",
            "字面列表集非空",
            "非空字面列表集非空",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl PowerSetNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowerSetNonempty",
            "Power Set Nonempty",
            "Verified by the power Set Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowerSetNonempty",
            "幂集非空",
            "任意集合的幂集非空",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

impl OneSideInfinityIntervalNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalNonempty",
            "One Side Infinity Interval Nonempty",
            "Verified by the one Side Infinity Interval Nonempty builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OneSideInfinityIntervalNonempty",
            "单侧无穷区间非空",
            "单侧无穷实区间非空",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

