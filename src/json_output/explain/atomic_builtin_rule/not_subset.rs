//! Leaf explain for atomic family group `not_subset`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_subset::{
    FromKnownNotSupersetBuiltinRuleProof,
    NotSubsetFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl NotSubsetFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownNotSuperset(p) => p.rule_name_and_message_vi(),
        }
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownNotSuperset(p) => p.premise_proof.cite_fact_id(),
        }
    }
}

impl FromKnownNotSupersetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "From Known Not Superset",
            "Duality: known `not B $superset A` proves `not A $subset B`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "已知非超集",
            "目标由已知的非超集事实推出",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由已知非包含關係",
            "對偶性：已知 `not B $superset A` 可證 `not A $subset B`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Depuis un non-sur-ensemble connu",
            "Dualité : `not B $superset A` connu prouve `not A $subset B`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Из известного отсутствия надмножества",
            "Двойственность: известное `not B $superset A` доказывает `not A $subset B`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desde no superconjunto conocido",
            "Dualidad: `not B $superset A` conocido prueba `not A $subset B`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "من عدم احتواء معلوم",
            "الثنائية: `not B $superset A` المعلومة تثبت `not A $subset B`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の非包含関係から",
            "双対性：既知の `not B $superset A` から `not A $subset B` を証明します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 비상위집합에서",
            "쌍대성: 알려진 `not B $superset A`로 `not A $subset B`를 증명합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Từ quan hệ không là tập cha đã biết",
            "Đối ngẫu: `not B $superset A` đã biết chứng minh `not A $subset B`",
        )
    }

    pub fn rule_name_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_name_and_message_en(),
            OutputLanguage::Chinese => self.rule_name_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_name_and_message_zh_hant(),
            OutputLanguage::French => self.rule_name_and_message_fr(),
            OutputLanguage::Russian => self.rule_name_and_message_ru(),
            OutputLanguage::Spanish => self.rule_name_and_message_es(),
            OutputLanguage::Arabic => self.rule_name_and_message_ar(),
            OutputLanguage::Japanese => self.rule_name_and_message_ja(),
            OutputLanguage::Korean => self.rule_name_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_name_and_message_vi(),
        }
    }
}
