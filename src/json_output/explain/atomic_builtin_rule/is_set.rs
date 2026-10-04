//! Leaf explain for atomic family group `is_set`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_set::{
    IsSetAlwaysTrueBuiltinRuleProof,
    IsSetFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl IsSetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_en(),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_zh(),
        }
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_zh_hant(),
        }
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_fr(),
        }
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_ru(),
        }
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_es(),
        }
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_ar(),
        }
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_ja(),
        }
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_ko(),
        }
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message_vi(),
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
            Self::AlwaysTrue(_) => None,
        }
    }
}

impl IsSetAlwaysTrueBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "Always True",
            "Verified by the always True builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AlwaysTrue", "恒为真", "「是集合」目标恒成立")
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("AlwaysTrue", "恆為真", "由恆為真內建規則驗證")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "Toujours vrai",
            "Vérifié par la règle intégrée de vérité constante",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "Всегда истинно",
            "Проверено встроенным правилом постоянной истинности",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "Siempre verdadero",
            "Verificado por la regla incorporada de verdad constante",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "صحيح دائمًا",
            "تم التحقق بقاعدة الصحة الدائمة المدمجة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "常に真",
            "常に真となる組み込み規則で検証しました",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "항상 참",
            "항상 참인 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "AlwaysTrue",
            "Luôn đúng",
            "Đã kiểm chứng bằng quy tắc tích hợp luôn đúng",
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
