//! Leaf explain for atomic family group `not_subset`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_subset::{
    FromKnownNotSupersetBuiltinRuleProof,
    NotSubsetFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotSubsetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownNotSuperset(p) => p.premise_proof.cite_fact_id(),
        }
    }
}

impl FromKnownNotSupersetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownNotSuperset",
            "From Known Not Superset",
            "Duality: known `not B $superset A` proves `not A $subset B`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownNotSuperset",
            "已知非超集",
            "目标由已知的非超集事实推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FromKnownNotSuperset",
                "由已知非包含關係",
                "對偶性：已知 `not B $superset A` 可證 `not A $subset B`",
            ),
            OutputLanguage::French => text(
                "FromKnownNotSuperset",
                "Depuis un non-sur-ensemble connu",
                "Dualité : `not B $superset A` connu prouve `not A $subset B`",
            ),
            OutputLanguage::Russian => text(
                "FromKnownNotSuperset",
                "Из известного отсутствия надмножества",
                "Двойственность: известное `not B $superset A` доказывает `not A $subset B`",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownNotSuperset",
                "Desde no superconjunto conocido",
                "Dualidad: `not B $superset A` conocido prueba `not A $subset B`",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownNotSuperset",
                "من عدم احتواء معلوم",
                "الثنائية: `not B $superset A` المعلومة تثبت `not A $subset B`",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownNotSuperset",
                "既知の非包含関係から",
                "双対性：既知の `not B $superset A` から `not A $subset B` を証明します",
            ),
            OutputLanguage::Korean => text(
                "FromKnownNotSuperset",
                "알려진 비상위집합에서",
                "쌍대성: 알려진 `not B $superset A`로 `not A $subset B`를 증명합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownNotSuperset",
                "Từ quan hệ không là tập cha đã biết",
                "Đối ngẫu: `not B $superset A` đã biết chứng minh `not A $subset B`",
            ),
        }
    }
}
