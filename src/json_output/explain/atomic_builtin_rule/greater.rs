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
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message(lang),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::FromKnownLess(p) => p.rule_id_and_message(lang),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::FromPositiveRealMembership(p) => p.rule_id_and_message(lang),
            Self::NativeEulerGreaterZero(p) => p.rule_id_and_message(lang),
            Self::NativeEulerGreaterOne(_) => match lang {
                OutputLanguage::English => text(
                    "NativeEulerGreaterOne",
                    "Euler constant exceeds one",
                    "The native Euler constant satisfies e > 1",
                ),
                OutputLanguage::ChineseTraditional => text(
                    "NativeEulerGreaterOne",
                    "Euler 常數大於一",
                    "內建 Euler 常數滿足 e > 1",
                ),
                OutputLanguage::French => text(
                    "NativeEulerGreaterOne",
                    "La constante d'Euler dépasse un",
                    "La constante d'Euler native vérifie e > 1",
                ),
                OutputLanguage::Russian => text(
                    "NativeEulerGreaterOne",
                    "Константа Эйлера больше единицы",
                    "Встроенная константа Эйлера удовлетворяет e > 1",
                ),
                OutputLanguage::Spanish => text(
                    "NativeEulerGreaterOne",
                    "La constante de Euler supera uno",
                    "La constante nativa de Euler cumple e > 1",
                ),
                OutputLanguage::Arabic => text(
                    "NativeEulerGreaterOne",
                    "ثابت أويلر أكبر من واحد",
                    "ثابت أويلر الأصلي يحقق e > 1",
                ),
                OutputLanguage::Japanese => text(
                    "NativeEulerGreaterOne",
                    "オイラーの定数は一より大きい",
                    "組み込みのオイラー定数は e > 1 を満たします",
                ),
                OutputLanguage::Korean => text(
                    "NativeEulerGreaterOne",
                    "오일러 상수가 1보다 큼",
                    "내장 오일러 상수는 e > 1을 만족합니다",
                ),
                OutputLanguage::Vietnamese => text(
                    "NativeEulerGreaterOne",
                    "Hằng số Euler lớn hơn một",
                    "Hằng số Euler tích hợp thỏa e > 1",
                ),

                OutputLanguage::Chinese => text(
                    "NativeEulerGreaterOne",
                    "自然常数 e 大于一",
                    "内建自然常数满足 e > 1",
                ),
            },
            Self::NativePiGreaterZero(p) => p.rule_id_and_message(lang),
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
            "if both sides evaluate to decimals L, R with L > R,",
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
            OutputLanguage::ChineseTraditional => {
        text(
            "ClosedNumericComparison",
            "封閉數值比較",
            "兩邊求值為十進位數 L、R 且 L > R，則大於成立",
        )
    },
            OutputLanguage::French => {
        text(
            "ClosedNumericComparison",
            "Comparaison numérique fermée",
            "Si les deux membres donnent des décimaux L, R avec L > R, la comparaison est vérifiée",
        )
    },
            OutputLanguage::Russian => {
        text(
            "ClosedNumericComparison",
            "Сравнение замкнутых числовых выражений",
            "Если обе части дают десятичные значения L, R и L > R, сравнение подтверждено",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "ClosedNumericComparison",
            "Comparación numérica cerrada",
            "Si ambos lados dan decimales L, R con L > R, la comparación se verifica",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "ClosedNumericComparison",
            "مقارنة عددية مغلقة",
            "إذا قيّم الطرفان إلى عددين عشريين L وR مع L > R تتحقق المقارنة",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "ClosedNumericComparison",
            "閉じた数値式の比較",
            "両辺の評価値が小数 L、R で L > R なら比較は成立します",
        )
    },
            OutputLanguage::Korean => {
        text(
            "ClosedNumericComparison",
            "닫힌 수치 식 비교",
            "양변의 평가값이 소수 L, R이고 L > R이면 비교가 성립합니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "ClosedNumericComparison",
            "So sánh số đóng",
            "Nếu hai vế cho số thập phân L, R với L > R thì so sánh được xác nhận",
        )
    },

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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FromKnownLess", "由已知小於", "`>` 是 `<` 的反向關係")
            }
            OutputLanguage::French => text(
                "FromKnownLess",
                "Depuis une inégalité inférieure connue",
                "`>` est la réciproque de `<`",
            ),
            OutputLanguage::Russian => text(
                "FromKnownLess",
                "Из известного меньшего значения",
                "`>` является обратным отношением к `<`",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownLess",
                "Desde desigualdad menor conocida",
                "`>` es la relación inversa de `<`",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownLess",
                "من علاقة أصغر معلومة",
                "`>` هي العلاقة العكسية لـ `<`",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownLess",
                "既知の小なり関係から",
                "`>` は `<` の逆向きの関係です",
            ),
            OutputLanguage::Korean => text(
                "FromKnownLess",
                "알려진 작음 관계에서",
                "`>`는 `<`의 역방향 관계입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownLess",
                "Từ quan hệ nhỏ hơn đã biết",
                "`>` là quan hệ đảo của `<`",
            ),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AddRightCongruenceStrict",
                "右加法嚴格序保持",
                "右加數嚴格序保持：`a > b` ⇒ `a + c > b + c`",
            ),
            OutputLanguage::French => text(
                "AddRightCongruenceStrict",
                "Congruence stricte d'addition à droite",
                "Congruence stricte d'addition à droite : `a > b` ⇒ `a + c > b + c`",
            ),
            OutputLanguage::Russian => text(
                "AddRightCongruenceStrict",
                "Строгая конгруэнтность сложения справа",
                "Строгая конгруэнтность сложения справа: `a > b` ⇒ `a + c > b + c`",
            ),
            OutputLanguage::Spanish => text(
                "AddRightCongruenceStrict",
                "Congruencia estricta de suma derecha",
                "Congruencia estricta de suma derecha: `a > b` ⇒ `a + c > b + c`",
            ),
            OutputLanguage::Arabic => text(
                "AddRightCongruenceStrict",
                "تطابق جمع أيمن صارم",
                "تطابق جمع أيمن صارم: `a > b` ⇒ `a + c > b + c`",
            ),
            OutputLanguage::Japanese => text(
                "AddRightCongruenceStrict",
                "右加算の狭義合同性",
                "右加算の狭義合同性：`a > b` ⇒ `a + c > b + c`",
            ),
            OutputLanguage::Korean => text(
                "AddRightCongruenceStrict",
                "오른쪽 덧셈의 엄격한 합동",
                "오른쪽 덧셈 엄격한 합동: `a > b` ⇒ `a + c > b + c`",
            ),
            OutputLanguage::Vietnamese => text(
                "AddRightCongruenceStrict",
                "Tương hợp nghiêm ngặt cộng phải",
                "Tương hợp nghiêm ngặt cộng phải: `a > b` ⇒ `a + c > b + c`",
            ),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AddLeftCongruenceStrict",
                "左加法嚴格序保持",
                "左加數嚴格序保持：`a > b` ⇒ `c + a > c + b`",
            ),
            OutputLanguage::French => text(
                "AddLeftCongruenceStrict",
                "Congruence stricte d'addition à gauche",
                "Congruence stricte d'addition à gauche : `a > b` ⇒ `c + a > c + b`",
            ),
            OutputLanguage::Russian => text(
                "AddLeftCongruenceStrict",
                "Строгая конгруэнтность сложения слева",
                "Строгая конгруэнтность сложения слева: `a > b` ⇒ `c + a > c + b`",
            ),
            OutputLanguage::Spanish => text(
                "AddLeftCongruenceStrict",
                "Congruencia estricta de suma izquierda",
                "Congruencia estricta de suma izquierda: `a > b` ⇒ `c + a > c + b`",
            ),
            OutputLanguage::Arabic => text(
                "AddLeftCongruenceStrict",
                "تطابق جمع أيسر صارم",
                "تطابق جمع أيسر صارم: `a > b` ⇒ `c + a > c + b`",
            ),
            OutputLanguage::Japanese => text(
                "AddLeftCongruenceStrict",
                "左加算の狭義合同性",
                "左加算の狭義合同性：`a > b` ⇒ `c + a > c + b`",
            ),
            OutputLanguage::Korean => text(
                "AddLeftCongruenceStrict",
                "왼쪽 덧셈의 엄격한 합동",
                "왼쪽 덧셈 엄격한 합동: `a > b` ⇒ `c + a > c + b`",
            ),
            OutputLanguage::Vietnamese => text(
                "AddLeftCongruenceStrict",
                "Tương hợp nghiêm ngặt cộng trái",
                "Tương hợp nghiêm ngặt cộng trái: `a > b` ⇒ `c + a > c + b`",
            ),
        }
    }
}

impl MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "Mul Left Positive Monotone Strict",
            "`0 < k` and `a > b` ⇒ `k * a > k * b`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左边正数乘法保序（严格）",
            "正因子左边乘法保持严格序",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MulLeftPositiveMonotoneStrict",
                "左乘正數保持嚴格序",
                "`0 < k` 與 `a > b` ⇒ `k * a > k * b`",
            ),
            OutputLanguage::French => text(
                "MulLeftPositiveMonotoneStrict",
                "Monotonie stricte de multiplication positive à gauche",
                "`0 < k` et `a > b` ⇒ `k * a > k * b`",
            ),
            OutputLanguage::Russian => text(
                "MulLeftPositiveMonotoneStrict",
                "Строгая монотонность положительного умножения слева",
                "`0 < k` и `a > b` ⇒ `k * a > k * b`",
            ),
            OutputLanguage::Spanish => text(
                "MulLeftPositiveMonotoneStrict",
                "Monotonía estricta de multiplicación positiva izquierda",
                "`0 < k` y `a > b` ⇒ `k * a > k * b`",
            ),
            OutputLanguage::Arabic => text(
                "MulLeftPositiveMonotoneStrict",
                "رتابة صارمة للضرب الموجب الأيسر",
                "`0 < k` و`a > b` ⇒ `k * a > k * b`",
            ),
            OutputLanguage::Japanese => text(
                "MulLeftPositiveMonotoneStrict",
                "正数の左乗算の狭義単調性",
                "`0 < k` かつ `a > b` ⇒ `k * a > k * b`",
            ),
            OutputLanguage::Korean => text(
                "MulLeftPositiveMonotoneStrict",
                "양수 왼쪽 곱셈의 엄격한 단조성",
                "`0 < k` 및 `a > b` ⇒ `k * a > k * b`",
            ),
            OutputLanguage::Vietnamese => text(
                "MulLeftPositiveMonotoneStrict",
                "Đơn điệu nghiêm ngặt nhân dương bên trái",
                "`0 < k` và `a > b` ⇒ `k * a > k * b`",
            ),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MulRightPositiveMonotoneStrict",
                "右乘正數保持嚴格序",
                "右乘正因子保持嚴格序",
            ),
            OutputLanguage::French => text(
                "MulRightPositiveMonotoneStrict",
                "Monotonie stricte de multiplication positive à droite",
                "La multiplication à droite par un facteur positif préserve l'ordre strict",
            ),
            OutputLanguage::Russian => text(
                "MulRightPositiveMonotoneStrict",
                "Строгая монотонность положительного умножения справа",
                "Умножение справа на положительный множитель сохраняет строгий порядок",
            ),
            OutputLanguage::Spanish => text(
                "MulRightPositiveMonotoneStrict",
                "Monotonía estricta de multiplicación positiva derecha",
                "Multiplicar a la derecha por un factor positivo conserva el orden estricto",
            ),
            OutputLanguage::Arabic => text(
                "MulRightPositiveMonotoneStrict",
                "رتابة صارمة للضرب الموجب الأيمن",
                "الضرب الأيمن بعامل موجب يحفظ الترتيب الصارم",
            ),
            OutputLanguage::Japanese => text(
                "MulRightPositiveMonotoneStrict",
                "正数の右乗算の狭義単調性",
                "正の因子による右乗算は狭義順序を保ちます",
            ),
            OutputLanguage::Korean => text(
                "MulRightPositiveMonotoneStrict",
                "양수 오른쪽 곱셈의 엄격한 단조성",
                "양의 인자를 오른쪽에 곱하면 엄격한 순서가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "MulRightPositiveMonotoneStrict",
                "Đơn điệu nghiêm ngặt nhân dương bên phải",
                "Nhân bên phải với thừa số dương bảo toàn thứ tự nghiêm ngặt",
            ),
        }
    }
}

impl FromPositiveRealMembershipBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "From Positive Real Membership",
            "`x $in R+` ⇒ `x > 0`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromPositiveRealMembership",
            "由正实数成员推出",
            "正实数成员蕴含严格大于零",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FromPositiveRealMembership",
                "由正實數成員關係",
                "`x $in R+` ⇒ `x > 0`",
            ),
            OutputLanguage::French => text(
                "FromPositiveRealMembership",
                "Depuis l'appartenance aux réels positifs",
                "`x $in R+` ⇒ `x > 0`",
            ),
            OutputLanguage::Russian => text(
                "FromPositiveRealMembership",
                "Из принадлежности положительным вещественным",
                "`x $in R+` ⇒ `x > 0`",
            ),
            OutputLanguage::Spanish => text(
                "FromPositiveRealMembership",
                "Desde pertenencia a reales positivos",
                "`x $in R+` ⇒ `x > 0`",
            ),
            OutputLanguage::Arabic => text(
                "FromPositiveRealMembership",
                "من انتماء للأعداد الحقيقية الموجبة",
                "`x $in R+` ⇒ `x > 0`",
            ),
            OutputLanguage::Japanese => text(
                "FromPositiveRealMembership",
                "正の実数への所属から",
                "`x $in R+` ⇒ `x > 0`",
            ),
            OutputLanguage::Korean => text(
                "FromPositiveRealMembership",
                "양의 실수 소속에서",
                "`x $in R+` ⇒ `x > 0`",
            ),
            OutputLanguage::Vietnamese => text(
                "FromPositiveRealMembership",
                "Từ sự thuộc về số thực dương",
                "`x $in R+` ⇒ `x > 0`",
            ),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NativeEulerGreaterZero",
                "內建 Euler 常數大於零",
                "內建 Euler 常數嚴格為正：`e > 0`",
            ),
            OutputLanguage::French => text(
                "NativeEulerGreaterZero",
                "Constante d'Euler native positive",
                "La constante d'Euler native est strictement positive : `e > 0`",
            ),
            OutputLanguage::Russian => text(
                "NativeEulerGreaterZero",
                "Положительная встроенная константа Эйлера",
                "Встроенная константа Эйлера строго положительна: `e > 0`",
            ),
            OutputLanguage::Spanish => text(
                "NativeEulerGreaterZero",
                "Constante nativa de Euler positiva",
                "La constante nativa de Euler es estrictamente positiva: `e > 0`",
            ),
            OutputLanguage::Arabic => text(
                "NativeEulerGreaterZero",
                "ثابت أويلر الأصلي موجب",
                "ثابت أويلر الأصلي موجب تمامًا: `e > 0`",
            ),
            OutputLanguage::Japanese => text(
                "NativeEulerGreaterZero",
                "組み込みのオイラー定数の正値性",
                "組み込みのオイラー定数は厳密に正です：`e > 0`",
            ),
            OutputLanguage::Korean => text(
                "NativeEulerGreaterZero",
                "내장 오일러 상수의 양수성",
                "내장 오일러 상수는 엄격히 양수입니다: `e > 0`",
            ),
            OutputLanguage::Vietnamese => text(
                "NativeEulerGreaterZero",
                "Hằng số Euler tích hợp dương",
                "Hằng số Euler tích hợp dương nghiêm ngặt: `e > 0`",
            ),
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

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NativePiGreaterZero",
                "內建 Pi 常數大於零",
                "內建 Pi 常數嚴格為正：`pi > 0`",
            ),
            OutputLanguage::French => text(
                "NativePiGreaterZero",
                "Constante pi native positive",
                "La constante pi native est strictement positive : `pi > 0`",
            ),
            OutputLanguage::Russian => text(
                "NativePiGreaterZero",
                "Положительная встроенная константа pi",
                "Встроенная константа pi строго положительна: `pi > 0`",
            ),
            OutputLanguage::Spanish => text(
                "NativePiGreaterZero",
                "Constante nativa pi positiva",
                "La constante nativa pi es estrictamente positiva: `pi > 0`",
            ),
            OutputLanguage::Arabic => text(
                "NativePiGreaterZero",
                "ثابت pi الأصلي موجب",
                "ثابت pi الأصلي موجب تمامًا: `pi > 0`",
            ),
            OutputLanguage::Japanese => text(
                "NativePiGreaterZero",
                "組み込みの円周率の正値性",
                "組み込みの円周率は厳密に正です：`pi > 0`",
            ),
            OutputLanguage::Korean => text(
                "NativePiGreaterZero",
                "내장 pi 상수의 양수성",
                "내장 pi 상수는 엄격히 양수입니다: `pi > 0`",
            ),
            OutputLanguage::Vietnamese => text(
                "NativePiGreaterZero",
                "Hằng số pi tích hợp dương",
                "Hằng số pi tích hợp dương nghiêm ngặt: `pi > 0`",
            ),
        }
    }
}
