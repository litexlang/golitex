//! Leaf explain for atomic family group `is_tuple`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_tuple::{
    IsTupleFactSearchProofByBuiltinRule,
    TupleLiteralBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl IsTupleFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::TupleLiteral(_) => None,
        }
    }
}

impl TupleLiteralBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "TupleLiteral",
            "Tuple Literal",
            "Verified by the tuple Literal builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("TupleLiteral", "元组字面量", "元组字面量形状成立")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("TupleLiteral", "元組字面值", "由元組字面值內建規則驗證")
            }
            OutputLanguage::French => text(
                "TupleLiteral",
                "Tuple littéral",
                "Vérifié par la règle intégrée du tuple littéral",
            ),
            OutputLanguage::Russian => text(
                "TupleLiteral",
                "Литерал кортежа",
                "Проверено встроенным правилом литерала кортежа",
            ),
            OutputLanguage::Spanish => text(
                "TupleLiteral",
                "Tupla literal",
                "Verificado por la regla incorporada de tupla literal",
            ),
            OutputLanguage::Arabic => text(
                "TupleLiteral",
                "صف حرفي",
                "تم التحقق بقاعدة الصف الحرفي المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "TupleLiteral",
                "タプルリテラル",
                "タプルリテラルの組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "TupleLiteral",
                "튜플 리터럴",
                "튜플 리터럴 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "TupleLiteral",
                "Bộ literal",
                "Đã kiểm chứng bằng quy tắc tích hợp bộ literal",
            ),
        }
    }
}
