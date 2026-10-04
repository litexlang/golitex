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
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::AlwaysTrue(p) => p.rule_id_and_message(lang),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AlwaysTrue", "恆為真", "由恆為真內建規則驗證")
            }
            OutputLanguage::French => text(
                "AlwaysTrue",
                "Toujours vrai",
                "Vérifié par la règle intégrée de vérité constante",
            ),
            OutputLanguage::Russian => text(
                "AlwaysTrue",
                "Всегда истинно",
                "Проверено встроенным правилом постоянной истинности",
            ),
            OutputLanguage::Spanish => text(
                "AlwaysTrue",
                "Siempre verdadero",
                "Verificado por la regla incorporada de verdad constante",
            ),
            OutputLanguage::Arabic => text(
                "AlwaysTrue",
                "صحيح دائمًا",
                "تم التحقق بقاعدة الصحة الدائمة المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "AlwaysTrue",
                "常に真",
                "常に真となる組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "AlwaysTrue",
                "항상 참",
                "항상 참인 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AlwaysTrue",
                "Luôn đúng",
                "Đã kiểm chứng bằng quy tắc tích hợp luôn đúng",
            ),
        }
    }
}
