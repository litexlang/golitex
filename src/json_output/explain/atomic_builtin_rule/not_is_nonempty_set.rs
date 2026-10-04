//! Leaf explain for atomic family group `not_is_nonempty_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_is_nonempty_set::{
    EmptyListSetNotNonemptyBuiltinRuleProof,
    NotIsNonemptySetFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotIsNonemptySetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_en(),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_zh(),
        }
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_zh_hant(),
        }
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_fr(),
        }
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_ru(),
        }
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_es(),
        }
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_ar(),
        }
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_ja(),
        }
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_ko(),
        }
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::EmptyListSet(p) => p.rule_id_and_message_vi(),
        }
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::EmptyListSet(_) => None,
        }
    }
}

impl EmptyListSetNotNonemptyBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "Empty List Set",
            "Verified by the empty List Set builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("EmptyListSet", "空列表集非非空", "空列表集不是非空集")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("EmptyListSet", "空列表集合", "由空列表集合內建規則驗證")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "Ensemble liste vide",
            "Vérifié par la règle intégrée d'ensemble liste vide",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "Пустое списочное множество",
            "Проверено встроенным правилом пустого списочного множества",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "Conjunto de lista vacío",
            "Verificado por la regla incorporada de conjunto de lista vacío",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "مجموعة قائمة خالية",
            "تم التحقق بقاعدة مجموعة القائمة الخالية المدمجة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "空のリスト集合",
            "空のリスト集合の組み込み規則で検証しました",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "빈 목록 집합",
            "빈 목록 집합 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "EmptyListSet",
            "Tập danh sách rỗng",
            "Đã kiểm chứng bằng quy tắc tích hợp tập danh sách rỗng",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => self.rule_id_and_message_zh_hant(),
            OutputLanguage::French => self.rule_id_and_message_fr(),
            OutputLanguage::Russian => self.rule_id_and_message_ru(),
            OutputLanguage::Spanish => self.rule_id_and_message_es(),
            OutputLanguage::Arabic => self.rule_id_and_message_ar(),
            OutputLanguage::Japanese => self.rule_id_and_message_ja(),
            OutputLanguage::Korean => self.rule_id_and_message_ko(),
            OutputLanguage::Vietnamese => self.rule_id_and_message_vi(),
        }
    }
}
