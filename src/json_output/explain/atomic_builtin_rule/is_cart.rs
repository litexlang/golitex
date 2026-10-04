//! Leaf explain for atomic family group `is_cart`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_cart::{
    CartConstructorBuiltinRuleProof,
    IsCartFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl IsCartFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::CartConstructor(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::CartConstructor(_) => None,
        }
    }
}

impl CartConstructorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "CartConstructor",
            "Cart Constructor",
            "Verified by the cart Constructor builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("CartConstructor", "笛卡尔积构造", "笛卡尔积构造子形状成立")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "CartConstructor",
                "笛卡兒積構造",
                "由笛卡兒積構造內建規則驗證",
            ),
            OutputLanguage::French => text(
                "CartConstructor",
                "Constructeur de produit cartésien",
                "Vérifié par la règle intégrée du constructeur de produit cartésien",
            ),
            OutputLanguage::Russian => text(
                "CartConstructor",
                "Конструктор декартова произведения",
                "Проверено встроенным правилом конструктора декартова произведения",
            ),
            OutputLanguage::Spanish => text(
                "CartConstructor",
                "Constructor de producto cartesiano",
                "Verificado por la regla incorporada del constructor de producto cartesiano",
            ),
            OutputLanguage::Arabic => text(
                "CartConstructor",
                "بنّاء حاصل الضرب الديكارتي",
                "تم التحقق بقاعدة بنّاء حاصل الضرب الديكارتي المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "CartConstructor",
                "直積の構成子",
                "直積の構成子の組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "CartConstructor",
                "데카르트 곱 생성자",
                "데카르트 곱 생성자 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "CartConstructor",
                "Hàm dựng tích Descartes",
                "Đã kiểm chứng bằng quy tắc tích hợp hàm dựng tích Descartes",
            ),
        }
    }
}
