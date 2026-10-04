//! Leaf explain for atomic family group `not_less_equal`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_less_equal::{
    ClosedNumericComparisonBuiltinRuleProof,
    NotLessEqualFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotLessEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message(lang),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::ClosedNumericComparison(_) => None,
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Closed Numeric Comparison",
            "if L > R as decimals, then `not (left <= right)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "封闭数值比较",
            "两边算出的数满足目标比较关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ClosedNumericComparison",
                "封閉數值比較",
                "十進位值 L > R 時，`not (left <= right)`",
            ),
            OutputLanguage::French => text(
                "ClosedNumericComparison",
                "Comparaison numérique fermée",
                "Si les valeurs décimales vérifient L > R, alors `not (left <= right)`",
            ),
            OutputLanguage::Russian => text(
                "ClosedNumericComparison",
                "Сравнение замкнутых числовых выражений",
                "Если десятичные значения удовлетворяют L > R, то `not (left <= right)`",
            ),
            OutputLanguage::Spanish => text(
                "ClosedNumericComparison",
                "Comparación numérica cerrada",
                "Si los valores decimales cumplen L > R, entonces `not (left <= right)`",
            ),
            OutputLanguage::Arabic => text(
                "ClosedNumericComparison",
                "مقارنة عددية مغلقة",
                "إذا كانت القيم العشرية تحقق L > R فإن `not (left <= right)`",
            ),
            OutputLanguage::Japanese => text(
                "ClosedNumericComparison",
                "閉じた数値式の比較",
                "小数値で L > R なら `not (left <= right)`",
            ),
            OutputLanguage::Korean => text(
                "ClosedNumericComparison",
                "닫힌 수치 식 비교",
                "소수 값이 L > R이면 `not (left <= right)`",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedNumericComparison",
                "So sánh số đóng",
                "Nếu giá trị thập phân thỏa L > R thì `not (left <= right)`",
            ),
        }
    }
}
