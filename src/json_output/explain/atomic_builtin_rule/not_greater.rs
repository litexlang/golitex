//! Leaf explain for atomic family group `not_greater`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_greater::{
    ClosedNumericComparisonBuiltinRuleProof,
    FromKnownLessBuiltinRuleProof,
    NotGreaterFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl NotGreaterFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message(lang),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::FromKnownLess(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::ClosedNumericComparison(_) => None,
            Self::FromKnownLess(p) => p.premise_proof.cite_fact_id(),
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Closed Numeric Comparison",
            "if L <= R as decimals, then `not (left > right)`",
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
                "十進位值 L <= R 時，`not (left > right)`",
            ),
            OutputLanguage::French => text(
                "ClosedNumericComparison",
                "Comparaison numérique fermée",
                "Si les valeurs décimales vérifient L <= R, alors `not (left > right)`",
            ),
            OutputLanguage::Russian => text(
                "ClosedNumericComparison",
                "Сравнение замкнутых числовых выражений",
                "Если десятичные значения удовлетворяют L <= R, то `not (left > right)`",
            ),
            OutputLanguage::Spanish => text(
                "ClosedNumericComparison",
                "Comparación numérica cerrada",
                "Si los valores decimales cumplen L <= R, entonces `not (left > right)`",
            ),
            OutputLanguage::Arabic => text(
                "ClosedNumericComparison",
                "مقارنة عددية مغلقة",
                "إذا كانت القيم العشرية تحقق L <= R فإن `not (left > right)`",
            ),
            OutputLanguage::Japanese => text(
                "ClosedNumericComparison",
                "閉じた数値式の比較",
                "小数値で L <= R なら `not (left > right)`",
            ),
            OutputLanguage::Korean => text(
                "ClosedNumericComparison",
                "닫힌 수치 식 비교",
                "소수 값이 L <= R이면 `not (left > right)`",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedNumericComparison",
                "So sánh số đóng",
                "Nếu giá trị thập phân thỏa L <= R thì `not (left > right)`",
            ),
        }
    }
}

impl FromKnownLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "From Known Less",
            "`a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "已知严格小于",
            "目标由已知的严格小于事实推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FromKnownLess", "由已知小於", "`a < b` ⇒ `not (a > b)`")
            }
            OutputLanguage::French => text(
                "FromKnownLess",
                "Depuis une inégalité inférieure connue",
                "`a < b` ⇒ `not (a > b)`",
            ),
            OutputLanguage::Russian => text(
                "FromKnownLess",
                "Из известного меньшего значения",
                "`a < b` ⇒ `not (a > b)`",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownLess",
                "Desde desigualdad menor conocida",
                "`a < b` ⇒ `not (a > b)`",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownLess",
                "من علاقة أصغر معلومة",
                "`a < b` ⇒ `not (a > b)`",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownLess",
                "既知の小なり関係から",
                "`a < b` ⇒ `not (a > b)`",
            ),
            OutputLanguage::Korean => text(
                "FromKnownLess",
                "알려진 작음 관계에서",
                "`a < b` ⇒ `not (a > b)`",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownLess",
                "Từ quan hệ nhỏ hơn đã biết",
                "`a < b` ⇒ `not (a > b)`",
            ),
        }
    }
}
