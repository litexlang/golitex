//! Leaf explain for atomic family group `greater`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater::{
    AddLeftCongruenceStrictBuiltinRuleProof,
    AddRightCongruenceStrictBuiltinRuleProof,
    ClosedNumericComparisonBuiltinRuleProof,
    FromKnownLessBuiltinRuleProof,
    FromPositiveRealMembershipBuiltinRuleProof,
    GreaterFactSearchProofByBuiltinRule,
    MulLeftPositiveMonotoneStrictBuiltinRuleProof,
    MulRightPositiveMonotoneStrictBuiltinRuleProof,
    NativeEulerGreaterZeroBuiltinRuleProof,
    NativePiGreaterZeroBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl GreaterFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_en(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_en(),
            Self::FromKnownLess(p) => p.rule_id_and_message_en(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_en(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_en(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_en(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_en(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_en(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_en(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "Euler constant exceeds one",
                "The native Euler constant satisfies e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_en(),
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_zh(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_zh(),
            Self::FromKnownLess(p) => p.rule_id_and_message_zh(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_zh(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_zh(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_zh(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_zh(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_zh(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_zh(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "自然常数 e 大于一",
                "内建自然常数满足 e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_zh(),
        }
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_zh_hant(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_zh_hant(),
            Self::FromKnownLess(p) => p.rule_id_and_message_zh_hant(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_zh_hant(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_zh_hant(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_zh_hant(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "Euler 常數大於一",
                "內建 Euler 常數滿足 e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_zh_hant(),
        }
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_fr(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_fr(),
            Self::FromKnownLess(p) => p.rule_id_and_message_fr(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_fr(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_fr(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_fr(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_fr(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_fr(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_fr(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "La constante d'Euler dépasse un",
                "La constante d'Euler native vérifie e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_fr(),
        }
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ru(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ru(),
            Self::FromKnownLess(p) => p.rule_id_and_message_ru(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ru(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ru(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ru(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ru(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_ru(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_ru(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "Константа Эйлера больше единицы",
                "Встроенная константа Эйлера удовлетворяет e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_ru(),
        }
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_es(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_es(),
            Self::FromKnownLess(p) => p.rule_id_and_message_es(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_es(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_es(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_es(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_es(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_es(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_es(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "La constante de Euler supera uno",
                "La constante nativa de Euler cumple e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_es(),
        }
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ar(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ar(),
            Self::FromKnownLess(p) => p.rule_id_and_message_ar(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ar(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ar(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ar(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ar(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_ar(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_ar(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "ثابت أويلر أكبر من واحد",
                "ثابت أويلر الأصلي يحقق e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_ar(),
        }
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ja(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ja(),
            Self::FromKnownLess(p) => p.rule_id_and_message_ja(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ja(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ja(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ja(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ja(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_ja(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_ja(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "オイラーの定数は一より大きい",
                "組み込みのオイラー定数は e > 1 を満たします",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_ja(),
        }
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_ko(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_ko(),
            Self::FromKnownLess(p) => p.rule_id_and_message_ko(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_ko(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_ko(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_ko(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_ko(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_ko(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_ko(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "오일러 상수가 1보다 큼",
                "내장 오일러 상수는 e > 1을 만족합니다",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_ko(),
        }
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message_vi(),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message_vi(),
            Self::FromKnownLess(p) => p.rule_id_and_message_vi(),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message_vi(),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message_vi(),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message_vi(),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message_vi(),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message_vi(),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message_vi(),
            Self::NativeEulerGreaterOne(_) => text(
                "NativeEulerGreaterOne",
                "Hằng số Euler lớn hơn một",
                "Hằng số Euler tích hợp thỏa e > 1",
            ),
            Self::NativePiGreaterZero(p) => p.rule_id_and_message_vi(),
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
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::ClosedNumericComparison(_) => None,
            Self::FromKnownLess(p) => p.premise_proof.cite_fact_id(),
            Self::AddRightCongruenceStrict(_) => None,
            Self::AddLeftCongruenceStrict(_) => None,
            Self::MulLeftPositiveMonotoneStrict(_) => None,
            Self::MulRightPositiveMonotoneStrict(_) => None,
            Self::FromPositiveRealMembership(_) => None,
            Self::NativeEulerGreaterZero(_) => None,
            Self::NativeEulerGreaterOne(_) => None,
            Self::NativePiGreaterZero(_) => None,
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Closed Numeric Comparison",
            "Both closed expressions evaluate to numbers, and the left value is strictly greater than the right",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "封闭数值比较",
            "两边算出的数满足目标比较关系",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "封閉數值比較",
            "兩邊求值為十進位數 L、R 且 L > R，則大於成立",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Comparaison numérique fermée",
            "Si les deux membres donnent des décimaux L, R avec L > R, la comparaison est vérifiée",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Сравнение замкнутых числовых выражений",
            "Если обе части дают десятичные значения L, R и L > R, сравнение подтверждено",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Comparación numérica cerrada",
            "Si ambos lados dan decimales L, R con L > R, la comparación se verifica",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "مقارنة عددية مغلقة",
            "إذا قيّم الطرفان إلى عددين عشريين L وR مع L > R تتحقق المقارنة",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "閉じた数値式の比較",
            "両辺の評価値が小数 L、R で L > R なら比較は成立します",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "닫힌 수치 식 비교",
            "양변의 평가값이 소수 L, R이고 L > R이면 비교가 성립합니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "So sánh số đóng",
            "Nếu hai vế cho số thập phân L, R với L > R thì so sánh được xác nhận",
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

impl FromKnownLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "From Known Less",
            "`>` is the converse of `<`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "已知严格小于",
            "目标由已知的严格小于事实推出",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("FromKnownLess", "由已知小於", "`>` 是 `<` 的反向關係")
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "Depuis une inégalité inférieure connue",
            "`>` est la réciproque de `<`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "Из известного меньшего значения",
            "`>` является обратным отношением к `<`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "Desde desigualdad menor conocida",
            "`>` es la relación inversa de `<`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "من علاقة أصغر معلومة",
            "`>` هي العلاقة العكسية لـ `<`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "既知の小なり関係から",
            "`>` は `<` の逆向きの関係です",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "알려진 작음 관계에서",
            "`>`는 `<`의 역방향 관계입니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "Từ quan hệ nhỏ hơn đã biết",
            "`>` là quan hệ đảo của `<`",
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

impl AddRightCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Add Right Congruence Strict",
            "Right addend congruence (strict): `a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右边加法同余（严格）",
            "严格序在右边加同一项后保持",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右加法嚴格序保持",
            "右加數嚴格序保持：`a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Congruence stricte d'addition à droite",
            "Congruence stricte d'addition à droite : `a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Строгая конгруэнтность сложения справа",
            "Строгая конгруэнтность сложения справа: `a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Congruencia estricta de suma derecha",
            "Congruencia estricta de suma derecha: `a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "تطابق جمع أيمن صارم",
            "تطابق جمع أيمن صارم: `a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右加算の狭義合同性",
            "右加算の狭義合同性：`a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "오른쪽 덧셈의 엄격한 합동",
            "오른쪽 덧셈 엄격한 합동: `a > b` ⇒ `a + c > b + c`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Tương hợp nghiêm ngặt cộng phải",
            "Tương hợp nghiêm ngặt cộng phải: `a > b` ⇒ `a + c > b + c`",
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

impl AddLeftCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Add Left Congruence Strict",
            "Left addend congruence (strict): `a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "左边加法同余（严格）",
            "严格序在左边加同一项后保持",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "左加法嚴格序保持",
            "左加數嚴格序保持：`a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Congruence stricte d'addition à gauche",
            "Congruence stricte d'addition à gauche : `a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Строгая конгруэнтность сложения слева",
            "Строгая конгруэнтность сложения слева: `a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Congruencia estricta de suma izquierda",
            "Congruencia estricta de suma izquierda: `a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "تطابق جمع أيسر صارم",
            "تطابق جمع أيسر صارم: `a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "左加算の狭義合同性",
            "左加算の狭義合同性：`a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "왼쪽 덧셈의 엄격한 합동",
            "왼쪽 덧셈 엄격한 합동: `a > b` ⇒ `c + a > c + b`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Tương hợp nghiêm ngặt cộng trái",
            "Tương hợp nghiêm ngặt cộng trái: `a > b` ⇒ `c + a > c + b`",
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

impl MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Left multiplication by a positive factor preserves strict order",
            "`0 < k` and `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左乘正数保持严格大小关系",
            "正因子左边乘法保持严格序",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左乘正數保持嚴格大小關係",
            "`0 < k` 與 `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Multiplication à gauche par un positif et ordre strict",
            "Multiplier à gauche par un facteur strictement positif préserve l’ordre strict: `0 < k` ∧ `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Умножение слева на положительное число сохраняет строгий порядок",
            "`0 < k` и `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Multiplicación izquierda por un positivo conserva el orden estricto",
            "La propiedad «Multiplicación izquierda por un positivo conserva el orden estricto» se expresa como: k > 0 ∧ a > b ⇒ k·a > k·b",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "الضرب من اليسار في موجب يحفظ الترتيب الصارم",
            "`0 < k` و`a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "正の数の左乗算による厳密な大小関係の保存",
            "`0 < k` かつ `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "양수의 왼쪽 곱셈에 따른 엄격한 순서 보존",
            "`0 < k` 및 `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Nhân bên trái với số dương bảo toàn thứ tự nghiêm ngặt",
            "`0 < k` và `a > b` ⇒ `k * a > k * b`",
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

impl MulRightPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Mul Right Positive Monotone Strict",
            "Right multiplication by a positive factor preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "右边正数乘法保序（严格）",
            "正因子右边乘法保持严格序",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "右乘正數保持嚴格序",
            "右乘正因子保持嚴格序",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Monotonie stricte de multiplication positive à droite",
            "La multiplication à droite par un facteur positif préserve l'ordre strict",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Строгая монотонность положительного умножения справа",
            "Умножение справа на положительный множитель сохраняет строгий порядок",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Monotonía estricta de multiplicación positiva derecha",
            "Multiplicar a la derecha por un factor positivo conserva el orden estricto",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "رتابة صارمة للضرب الموجب الأيمن",
            "الضرب الأيمن بعامل موجب يحفظ الترتيب الصارم",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "正数の右乗算の狭義単調性",
            "正の因子による右乗算は狭義順序を保ちます",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "양수 오른쪽 곱셈의 엄격한 단조성",
            "양의 인자를 오른쪽에 곱하면 엄격한 순서가 보존됩니다",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "Đơn điệu nghiêm ngặt nhân dương bên phải",
            "Nhân bên phải với thừa số dương bảo toàn thứ tự nghiêm ngặt",
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

impl FromPositiveRealMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "Positive-real membership implies positivity",
            "The Positive-real membership implies positivity law gives: x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "正实数集合成员为正",
            "正实数集合成员为正可写为：x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "正實數集合成員為正",
            "正實數集合成員為正可寫為：x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "Appartenance aux réels positifs et positivité",
            "La propriété « Appartenance aux réels positifs et positivité » donne: x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "Принадлежность положительным вещественным означает положительность",
            "Свойство «Принадлежность положительным вещественным означает положительность» выражается равенством: x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "Pertenencia a reales positivos implica positividad",
            "La propiedad «Pertenencia a reales positivos implica positividad» se expresa como: x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "الانتماء إلى الأعداد الحقيقية الموجبة يستلزم الإيجابية",
            "تُكتب خاصية «الانتماء إلى الأعداد الحقيقية الموجبة يستلزم الإيجابية» كما يلي: x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "正の実数集合への所属による正値性",
            "正の実数集合への所属による正値性は次の式で表されます：x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "양의 실수 집합 소속에 따른 양수성",
            "양의 실수 집합 소속에 따른 양수성은 다음 식으로 나타납니다: x ∈ R+ ⇒ x > 0",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "Thuộc tập số thực dương suy ra dương",
            "Tính chất «Thuộc tập số thực dương suy ra dương» được biểu diễn bởi: x ∈ R+ ⇒ x > 0",
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

impl NativeEulerGreaterZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "Native Euler Greater Zero",
            "Native Euler constant is strictly positive: `e > 0`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "自然常数 e 大于零",
            "自然常数 e 严格大于零",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "內建 Euler 常數大於零",
            "內建 Euler 常數嚴格為正：`e > 0`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "Constante d'Euler native positive",
            "La constante d'Euler native est strictement positive : `e > 0`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "Положительная встроенная константа Эйлера",
            "Встроенная константа Эйлера строго положительна: `e > 0`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "Constante nativa de Euler positiva",
            "La constante nativa de Euler es estrictamente positiva: `e > 0`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "ثابت أويلر الأصلي موجب",
            "ثابت أويلر الأصلي موجب تمامًا: `e > 0`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "組み込みのオイラー定数の正値性",
            "組み込みのオイラー定数は厳密に正です：`e > 0`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "내장 오일러 상수의 양수성",
            "내장 오일러 상수는 엄격히 양수입니다: `e > 0`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NativeEulerGreaterZero",
            "Hằng số Euler tích hợp dương",
            "Hằng số Euler tích hợp dương nghiêm ngặt: `e > 0`",
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

impl NativePiGreaterZeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "Native Pi Greater Zero",
            "Native Pi constant is strictly positive: `pi > 0`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "圆周率 π 大于零",
            "圆周率 π 严格大于零",
        )
    }

    pub fn rule_id_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "內建 Pi 常數大於零",
            "內建 Pi 常數嚴格為正：`pi > 0`",
        )
    }

    pub fn rule_id_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "Constante pi native positive",
            "La constante pi native est strictement positive : `pi > 0`",
        )
    }

    pub fn rule_id_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "Положительная встроенная константа pi",
            "Встроенная константа pi строго положительна: `pi > 0`",
        )
    }

    pub fn rule_id_and_message_es(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "Constante nativa pi positiva",
            "La constante nativa pi es estrictamente positiva: `pi > 0`",
        )
    }

    pub fn rule_id_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "ثابت pi الأصلي موجب",
            "ثابت pi الأصلي موجب تمامًا: `pi > 0`",
        )
    }

    pub fn rule_id_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "組み込みの円周率の正値性",
            "組み込みの円周率は厳密に正です：`pi > 0`",
        )
    }

    pub fn rule_id_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "내장 pi 상수의 양수성",
            "내장 pi 상수는 엄격히 양수입니다: `pi > 0`",
        )
    }

    pub fn rule_id_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "NativePiGreaterZero",
            "Hằng số pi tích hợp dương",
            "Hằng số pi tích hợp dương nghiêm ngặt: `pi > 0`",
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
