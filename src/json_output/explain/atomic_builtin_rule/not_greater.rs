//! Leaf explain for atomic family group `not_greater`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_greater::{
    ClosedNumericComparisonBuiltinRuleProof,
    FromKnownLessBuiltinRuleProof,
    NotGreaterFactSearchProofByBuiltinRule,
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl NotGreaterFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_en(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_en(),
            Self::FromKnownLess(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_zh(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_zh(),
            Self::FromKnownLess(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_zh_hant(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownLess(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_fr(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_fr(),
            Self::FromKnownLess(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ru(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ru(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_es(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_es(),
            Self::FromKnownLess(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ar(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ar(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ja(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ja(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ko(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ko(),
            Self::FromKnownLess(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_vi(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_vi(),
            Self::FromKnownLess(p) => p.rule_name_and_message_vi(),
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
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::ClosedNumericComparison(_) => None,
            Self::FromKnownLess(p) => p.premise_proof.cite_fact_id(),
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Closed Numeric Comparison",
            "Exact closed values show the left side is less than or equal, excluding strict greater-than",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("封闭数值比较", "两边算出的数满足目标比较关系")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("封閉數值比較", "十進位值 L <= R 時，`not (left > right)`")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Comparaison numérique fermée",
            "Si les valeurs décimales vérifient L <= R, alors `not (left > right)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сравнение замкнутых числовых выражений",
            "Если десятичные значения удовлетворяют L <= R, то `not (left > right)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Comparación numérica cerrada",
            "Si los valores decimales cumplen L <= R, entonces `not (left > right)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مقارنة عددية مغلقة",
            "إذا كانت القيم العشرية تحقق L <= R فإن `not (left > right)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "閉じた数値式の比較",
            "小数値で L <= R なら `not (left > right)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "닫힌 수치 식 비교",
            "소수 값이 L <= R이면 `not (left > right)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "So sánh số đóng",
            "Nếu giá trị thập phân thỏa L <= R thì `not (left > right)`",
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

impl FromKnownLessBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "From Known Less",
            "The From Known Less rule establishes the following relation: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("已知严格小于", "目标由已知的严格小于事实推出")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由已知小於",
            "由已知小於給出以下關係: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Depuis une inégalité inférieure connue",
            "La règle « Depuis une inégalité inférieure connue » établit la relation suivante: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Из известного меньшего значения",
            "Правило «Из известного меньшего значения» устанавливает следующее соотношение: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desde desigualdad menor conocida",
            "La regla «Desde desigualdad menor conocida» establece la siguiente relación: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "من علاقة أصغر معلومة",
            "تثبت قاعدة «من علاقة أصغر معلومة» العلاقة التالية: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の小なり関係から",
            "既知の小なり関係からにより次の関係が得られます: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 작음 관계에서",
            "알려진 작음 관계에서에 따라 다음 관계를 얻습니다: `a < b` ⇒ `not (a > b)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Từ quan hệ nhỏ hơn đã biết",
            "Quy tắc «Từ quan hệ nhỏ hơn đã biết» thiết lập quan hệ sau: `a < b` ⇒ `not (a > b)`",
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
