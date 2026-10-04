//! Explain + cite for `LessFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{
    FromKnownGreaterBuiltinRuleProof,
    LessFactSearchProofByBuiltinRule, FiniteSetSizeProperSubsetLtBuiltinRuleProof, AddLeftCongruenceStrictBuiltinRuleProof,
    AddRightCongruenceStrictBuiltinRuleProof, ArccotPrincipalLowerBoundBuiltinRuleProof,
    ArccotPrincipalUpperBoundBuiltinRuleProof, ArctanPrincipalLowerBoundBuiltinRuleProof,
    ArctanPrincipalUpperBoundBuiltinRuleProof, ClosedNumericComparisonBuiltinRuleProof,
    DivByGtOneLessSelfBuiltinRuleProof, DivMonotoneStrictSameNegDivisorBuiltinRuleProof,
    DivMonotoneStrictSamePosDivisorBuiltinRuleProof, EvenPowPositiveFromNonzeroBuiltinRuleProof,
    LessFromPosDifferenceBuiltinRuleProof, LessTransitivityBuiltinRuleProof,
    LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof,
    LogOrderPreservingStrictBuiltinRuleProof, LogPositiveFromBaseAndArgGtOneBuiltinRuleProof,
    ModRemainderStrictUpperBoundBuiltinRuleProof, MulLeftPositiveMonotoneStrictBuiltinRuleProof,
    MulRightPositiveMonotoneStrictBuiltinRuleProof, NumericLowerBoundWeakenLtBuiltinRuleProof,
    NumericUpperBoundWeakenLtBuiltinRuleProof, PosDifferenceFromLessBuiltinRuleProof,
    PositiveEvenGtOneBuiltinRuleProof, PowPositiveFromPositiveBaseBuiltinRuleProof,
    ProductBothPositiveBuiltinRuleProof, SqrtMonotoneIncreasingBuiltinRuleProof,
    SqrtPositiveBuiltinRuleProof, SubtractOneLessBuiltinRuleProof,
    SubtractPositiveClosedLessBuiltinRuleProof, SumBothPositiveBuiltinRuleProof,
    SumLeftNonnegativeRightStrictBuiltinRuleProof, SumLeftStrictRightNonnegativeBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromPositiveLiteralBoundBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl LessFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::FromKnownGreater(p) => p.rule_id_and_message(lang),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message(lang),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::PiMultipleComparison(_) => match lang {
                OutputLanguage::English => text(
                    "PiMultipleComparison",
                    "Exact pi coefficient order",
                    "pi is positive and the exact left rational coefficient is smaller",
                ),
                OutputLanguage::ChineseTraditional => text(
                    "PiMultipleComparison",
                    "精確 pi 係數序",
                    "pi 為正且精確左有理係數較小",
                ),
                OutputLanguage::French => text(
                    "PiMultipleComparison",
                    "Ordre exact des coefficients de pi",
                    "pi est positif et le coefficient rationnel exact de gauche est inférieur",
                ),
                OutputLanguage::Russian => text(
                    "PiMultipleComparison",
                    "Точный порядок коэффициентов pi",
                    "pi положительно, и точный левый рациональный коэффициент меньше",
                ),
                OutputLanguage::Spanish => text(
                    "PiMultipleComparison",
                    "Orden exacto de coeficientes de pi",
                    "pi es positivo y el coeficiente racional exacto izquierdo es menor",
                ),
                OutputLanguage::Arabic => text(
                    "PiMultipleComparison",
                    "ترتيب دقيق لمعاملات pi",
                    "pi موجب والمعامل النسبي الدقيق الأيسر أصغر",
                ),
                OutputLanguage::Japanese => text(
                    "PiMultipleComparison",
                    "正確な pi 係数の順序",
                    "pi は正で、正確な左の有理係数が小さいです",
                ),
                OutputLanguage::Korean => text(
                    "PiMultipleComparison",
                    "정확한 pi 계수 순서",
                    "pi는 양수이고 정확한 왼쪽 유리수 계수가 더 작습니다",
                ),
                OutputLanguage::Vietnamese => text(
                    "PiMultipleComparison",
                    "Thứ tự hệ số pi chính xác",
                    "pi dương và hệ số hữu tỉ chính xác bên trái nhỏ hơn",
                ),

                OutputLanguage::Chinese => text(
                    "PiMultipleComparison",
                    "pi 系数精确比较",
                    "pi 为正且左边的精确有理系数更小",
                ),
            },
            Self::SubtractOneLess(p) => p.rule_id_and_message(lang),
            Self::SubtractPositiveClosedLess(p) => p.rule_id_and_message(lang),
            Self::ArctanPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArctanPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::ArccotPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArccotPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::SumBothPositive(p) => p.rule_id_and_message(lang),
            Self::SumLeftStrictRightNonnegative(p) => p.rule_id_and_message(lang),
            Self::SumLeftNonnegativeRightStrict(p) => p.rule_id_and_message(lang),
            Self::ProductBothPositive(p) => p.rule_id_and_message(lang),
            Self::EvenPowPositiveFromNonzero(p) => p.rule_id_and_message(lang),
            Self::PowPositiveFromPositiveBase(p) => p.rule_id_and_message(lang),
            Self::SqrtPositive(p) => p.rule_id_and_message(lang),
            Self::SqrtMonotoneIncreasing(p) => p.rule_id_and_message(lang),
            Self::LogOrderPreservingStrict(p) => p.rule_id_and_message(lang),
            Self::LogPositiveFromBaseAndArgGtOne(p) => p.rule_id_and_message(lang),
            Self::LogNegativeFromBaseGtOneArgInUnitInterval(p) => p.rule_id_and_message(lang),
            Self::LessTransitivity(p) => p.rule_id_and_message(lang),
            Self::LessFromPosDifference(p) => p.rule_id_and_message(lang),
            Self::PosDifferenceFromLess(p) => p.rule_id_and_message(lang),
            Self::ModRemainderStrictUpperBound(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneStrictSamePosDivisor(p) => p.rule_id_and_message(lang),
            Self::DivByGtOneLessSelf(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneStrictSameNegDivisor(p) => p.rule_id_and_message(lang),
            Self::NumericLowerBoundWeakenLt(p) => p.rule_id_and_message(lang),
            Self::NumericUpperBoundWeakenLt(p) => p.rule_id_and_message(lang),
            Self::PositiveEvenGtOne(p) => p.rule_id_and_message(lang),
            Self::AddRightCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::AddLeftCongruenceStrict(p) => p.rule_id_and_message(lang),
            Self::MulLeftPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::MulRightPositiveMonotoneStrict(p) => p.rule_id_and_message(lang),
            Self::OrderSignFromPositiveLiteralBound(p) => p.rule_id_and_message(lang),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeProperSubsetLt(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::FromKnownGreater(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::LessTransitivity(_) => None,
            Self::LessFromPosDifference(p) => p.premise_proof.cite_fact_id(),
            Self::PosDifferenceFromLess(p) => p.premise_proof.cite_fact_id(),
            Self::NumericLowerBoundWeakenLt(p) => Some(p.cite_fact_id),
            Self::NumericUpperBoundWeakenLt(p) => Some(p.cite_fact_id),
            Self::OrderSignFromPositiveLiteralBound(p) => Some(p.cite_fact_id),
            Self::OrderFlipMulMinusOne(p) => p.premise_proof.cite_fact_id(),
            _ => None,
        }
    }
}

impl FiniteSetSizeProperSubsetLtBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FiniteSetSizeProperSubsetLt",
                "Proper finite subset cardinality",
                "A proper subset of a finite set has strictly smaller cardinality",
            ),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeProperSubsetLt",
                "有限真子集基數",
                "有限集合的真子集基數嚴格較小",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeProperSubsetLt",
                "Cardinal d'un sous-ensemble propre fini",
                "Un sous-ensemble propre d'un ensemble fini a un cardinal strictement inférieur",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeProperSubsetLt",
                "Мощность конечного собственного подмножества",
                "Собственное подмножество конечного множества имеет строго меньшую мощность",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeProperSubsetLt",
                "Cardinalidad de subconjunto propio finito",
                "Un subconjunto propio de conjunto finito tiene cardinalidad estrictamente menor",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeProperSubsetLt",
                "عدد عناصر مجموعة جزئية حقيقية منتهية",
                "المجموعة الجزئية الحقيقية لمجموعة منتهية عدد عناصرها أصغر تمامًا",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeProperSubsetLt",
                "有限真部分集合の濃度",
                "有限集合の真部分集合の濃度は厳密に小さいです",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeProperSubsetLt",
                "유한 진부분집합의 기수",
                "유한 집합의 진부분집합 기수는 엄격히 작습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeProperSubsetLt",
                "Lực lượng tập con thực sự hữu hạn",
                "Tập con thực sự của tập hữu hạn có lực lượng nhỏ hơn nghiêm ngặt",
            ),

            OutputLanguage::Chinese => text(
                "FiniteSetSizeProperSubsetLt",
                "有限真子集的基数严格更小",
                "有限集合的真子集具有严格更小的基数",
            ),
        }
    }
}

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "Closed numeric comparison",
            "Both sides are closed numbers and compare as stated",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ClosedNumericComparison",
            "封闭数值比较",
            "两边都是可计算的数，并满足所述比较",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ClosedNumericComparison",
                "封閉數值比較",
                "兩邊為封閉數值且符合所述比較",
            ),
            OutputLanguage::French => text(
                "ClosedNumericComparison",
                "Comparaison numérique fermée",
                "Les deux membres sont des nombres fermés et satisfont la comparaison indiquée",
            ),
            OutputLanguage::Russian => text(
                "ClosedNumericComparison",
                "Сравнение замкнутых числовых выражений",
                "Обе части являются замкнутыми числами и удовлетворяют указанному сравнению",
            ),
            OutputLanguage::Spanish => text(
                "ClosedNumericComparison",
                "Comparación numérica cerrada",
                "Ambos lados son números cerrados y cumplen la comparación indicada",
            ),
            OutputLanguage::Arabic => text(
                "ClosedNumericComparison",
                "مقارنة عددية مغلقة",
                "الطرفان عددان مغلقان ويحققان المقارنة المذكورة",
            ),
            OutputLanguage::Japanese => text(
                "ClosedNumericComparison",
                "閉じた数値式の比較",
                "両辺は閉じた数値であり、指定された比較を満たします",
            ),
            OutputLanguage::Korean => text(
                "ClosedNumericComparison",
                "닫힌 수치 식 비교",
                "양변은 닫힌 수이며 명시된 비교를 만족합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ClosedNumericComparison",
                "So sánh số đóng",
                "Hai vế là số đóng và thỏa so sánh đã nêu",
            ),
        }
    }
}

impl SubtractOneLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubtractOneLess",
            "n-1 < n",
            "Subtracting one yields a strictly smaller value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubtractOneLess", "n-1 < n", "减一得到严格更小的值")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SubtractOneLess", "n-1 < n", "減一得嚴格較小值")
            }
            OutputLanguage::French => text(
                "SubtractOneLess",
                "n-1 < n",
                "Soustraire un donne une valeur strictement inférieure",
            ),
            OutputLanguage::Russian => text(
                "SubtractOneLess",
                "n-1 < n",
                "Вычитание единицы даёт строго меньшее значение",
            ),
            OutputLanguage::Spanish => text(
                "SubtractOneLess",
                "n-1 < n",
                "Restar uno da un valor estrictamente menor",
            ),
            OutputLanguage::Arabic => text(
                "SubtractOneLess",
                "n-1 < n",
                "طرح واحد يعطي قيمة أصغر تمامًا",
            ),
            OutputLanguage::Japanese => text(
                "SubtractOneLess",
                "n-1 < n",
                "一を引くと厳密に小さい値になります",
            ),
            OutputLanguage::Korean => text(
                "SubtractOneLess",
                "n-1 < n",
                "1을 빼면 엄격히 작은 값이 됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SubtractOneLess",
                "n-1 < n",
                "Trừ một cho giá trị nhỏ hơn nghiêm ngặt",
            ),
        }
    }
}

impl SubtractPositiveClosedLessBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "SubtractPositiveClosedLess",
                "Subtract a positive constant",
                "Subtracting a closed exact positive value yields a smaller real value",
            ),
            OutputLanguage::ChineseTraditional => text(
                "SubtractPositiveClosedLess",
                "減去正常數",
                "減去封閉精確正值得較小實數值",
            ),
            OutputLanguage::French => text(
                "SubtractPositiveClosedLess",
                "Soustraction d'une constante positive",
                "Soustraire une valeur positive fermée exacte donne un réel plus petit",
            ),
            OutputLanguage::Russian => text(
                "SubtractPositiveClosedLess",
                "Вычитание положительной константы",
                "Вычитание точного замкнутого положительного значения даёт меньшее вещественное значение",
            ),
            OutputLanguage::Spanish => text(
                "SubtractPositiveClosedLess",
                "Restar constante positiva",
                "Restar un valor positivo cerrado exacto da un real menor",
            ),
            OutputLanguage::Arabic => text(
                "SubtractPositiveClosedLess",
                "طرح ثابت موجب",
                "طرح قيمة موجبة مغلقة دقيقة يعطي قيمة حقيقية أصغر",
            ),
            OutputLanguage::Japanese => text(
                "SubtractPositiveClosedLess",
                "正の定数の減算",
                "正確な閉じた正値を引くと小さい実数値になります",
            ),
            OutputLanguage::Korean => text(
                "SubtractPositiveClosedLess",
                "양의 상수 빼기",
                "정확한 닫힌 양의 값을 빼면 더 작은 실수 값이 됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SubtractPositiveClosedLess",
                "Trừ hằng dương",
                "Trừ giá trị dương đóng chính xác cho giá trị thực nhỏ hơn",
            ),

            OutputLanguage::Chinese => text(
                "SubtractPositiveClosedLess",
                "减去正的常数",
                "实数减去可精确计算的正数，结果严格更小",
            ),
        }
    }
}

impl ArctanPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "arctan lower bound",
            "arctan stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalLowerBound",
            "arctan 下界",
            "arctan 落在其主值下界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArctanPrincipalLowerBound",
                "arctan 下界",
                "arctan 不低於主值下界",
            ),
            OutputLanguage::French => text(
                "ArctanPrincipalLowerBound",
                "Borne inférieure de arctan",
                "arctan respecte sa borne principale inférieure",
            ),
            OutputLanguage::Russian => text(
                "ArctanPrincipalLowerBound",
                "Нижняя граница arctan",
                "arctan не ниже своей главной нижней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArctanPrincipalLowerBound",
                "Cota inferior de arctan",
                "arctan respeta su cota principal inferior",
            ),
            OutputLanguage::Arabic => text(
                "ArctanPrincipalLowerBound",
                "حد أدنى لـ arctan",
                "arctan يبقى ضمن حده الرئيسي الأدنى",
            ),
            OutputLanguage::Japanese => text(
                "ArctanPrincipalLowerBound",
                "arctan の下界",
                "arctan は主値の下界以上です",
            ),
            OutputLanguage::Korean => text(
                "ArctanPrincipalLowerBound",
                "arctan 하한",
                "arctan는 주값 하한 이상입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArctanPrincipalLowerBound",
                "Cận dưới arctan",
                "arctan giữ trong cận dưới chính",
            ),
        }
    }
}

impl ArctanPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "arctan upper bound",
            "arctan stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArctanPrincipalUpperBound",
            "arctan 上界",
            "arctan 落在其主值上界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArctanPrincipalUpperBound",
                "arctan 上界",
                "arctan 不高於主值上界",
            ),
            OutputLanguage::French => text(
                "ArctanPrincipalUpperBound",
                "Borne supérieure de arctan",
                "arctan respecte sa borne principale supérieure",
            ),
            OutputLanguage::Russian => text(
                "ArctanPrincipalUpperBound",
                "Верхняя граница arctan",
                "arctan не выше своей главной верхней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArctanPrincipalUpperBound",
                "Cota superior de arctan",
                "arctan respeta su cota principal superior",
            ),
            OutputLanguage::Arabic => text(
                "ArctanPrincipalUpperBound",
                "حد أعلى لـ arctan",
                "arctan يبقى ضمن حده الرئيسي الأعلى",
            ),
            OutputLanguage::Japanese => text(
                "ArctanPrincipalUpperBound",
                "arctan の上界",
                "arctan は主値の上界以下です",
            ),
            OutputLanguage::Korean => text(
                "ArctanPrincipalUpperBound",
                "arctan 상한",
                "arctan는 주값 상한 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArctanPrincipalUpperBound",
                "Cận trên arctan",
                "arctan giữ trong cận trên chính",
            ),
        }
    }
}

impl ArccotPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "arccot lower bound",
            "arccot stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalLowerBound",
            "arccot 下界",
            "arccot 落在其主值下界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArccotPrincipalLowerBound",
                "arccot 下界",
                "arccot 不低於主值下界",
            ),
            OutputLanguage::French => text(
                "ArccotPrincipalLowerBound",
                "Borne inférieure de arccot",
                "arccot respecte sa borne principale inférieure",
            ),
            OutputLanguage::Russian => text(
                "ArccotPrincipalLowerBound",
                "Нижняя граница arccot",
                "arccot не ниже своей главной нижней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArccotPrincipalLowerBound",
                "Cota inferior de arccot",
                "arccot respeta su cota principal inferior",
            ),
            OutputLanguage::Arabic => text(
                "ArccotPrincipalLowerBound",
                "حد أدنى لـ arccot",
                "arccot يبقى ضمن حده الرئيسي الأدنى",
            ),
            OutputLanguage::Japanese => text(
                "ArccotPrincipalLowerBound",
                "arccot の下界",
                "arccot は主値の下界以上です",
            ),
            OutputLanguage::Korean => text(
                "ArccotPrincipalLowerBound",
                "arccot 하한",
                "arccot는 주값 하한 이상입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArccotPrincipalLowerBound",
                "Cận dưới arccot",
                "arccot giữ trong cận dưới chính",
            ),
        }
    }
}

impl ArccotPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "arccot upper bound",
            "arccot stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccotPrincipalUpperBound",
            "arccot 上界",
            "arccot 落在其主值上界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArccotPrincipalUpperBound",
                "arccot 上界",
                "arccot 不高於主值上界",
            ),
            OutputLanguage::French => text(
                "ArccotPrincipalUpperBound",
                "Borne supérieure de arccot",
                "arccot respecte sa borne principale supérieure",
            ),
            OutputLanguage::Russian => text(
                "ArccotPrincipalUpperBound",
                "Верхняя граница arccot",
                "arccot не выше своей главной верхней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArccotPrincipalUpperBound",
                "Cota superior de arccot",
                "arccot respeta su cota principal superior",
            ),
            OutputLanguage::Arabic => text(
                "ArccotPrincipalUpperBound",
                "حد أعلى لـ arccot",
                "arccot يبقى ضمن حده الرئيسي الأعلى",
            ),
            OutputLanguage::Japanese => text(
                "ArccotPrincipalUpperBound",
                "arccot の上界",
                "arccot は主値の上界以下です",
            ),
            OutputLanguage::Korean => text(
                "ArccotPrincipalUpperBound",
                "arccot 상한",
                "arccot는 주값 상한 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArccotPrincipalUpperBound",
                "Cận trên arccot",
                "arccot giữ trong cận trên chính",
            ),
        }
    }
}

impl SumBothPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumBothPositive",
            "Sum of positives > 0",
            "A sum of positive terms is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumBothPositive", "正数和 > 0", "正项之和为正")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SumBothPositive", "正數和 > 0", "正項的和為正")
            }
            OutputLanguage::French => text(
                "SumBothPositive",
                "Somme de positifs > 0",
                "Une somme de termes positifs est positive",
            ),
            OutputLanguage::Russian => text(
                "SumBothPositive",
                "Сумма положительных > 0",
                "Сумма положительных членов положительна",
            ),
            OutputLanguage::Spanish => text(
                "SumBothPositive",
                "Suma de positivos > 0",
                "Una suma de términos positivos es positiva",
            ),
            OutputLanguage::Arabic => text(
                "SumBothPositive",
                "مجموع الموجبات > 0",
                "مجموع حدود موجبة موجب",
            ),
            OutputLanguage::Japanese => {
                text("SumBothPositive", "正数の和 > 0", "正の項の和は正です")
            }
            OutputLanguage::Korean => text(
                "SumBothPositive",
                "양수의 합 > 0",
                "양의 항의 합은 양수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SumBothPositive",
                "Tổng số dương > 0",
                "Tổng các hạng dương là dương",
            ),
        }
    }
}

impl SumLeftStrictRightNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "pos + nonneg > 0",
            "Strictly positive plus nonnegative is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SumLeftStrictRightNonnegative",
            "正 + 非负 > 0",
            "严格正加非负为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SumLeftStrictRightNonnegative",
                "正數 + 非負數 > 0",
                "嚴格正數加非負數為正",
            ),
            OutputLanguage::French => text(
                "SumLeftStrictRightNonnegative",
                "Positif + non-négatif > 0",
                "Strictement positif plus non-négatif est positif",
            ),
            OutputLanguage::Russian => text(
                "SumLeftStrictRightNonnegative",
                "Положительное + неотрицательное > 0",
                "Строго положительное плюс неотрицательное положительно",
            ),
            OutputLanguage::Spanish => text(
                "SumLeftStrictRightNonnegative",
                "Positivo + no negativo > 0",
                "Estrictamente positivo más no negativo es positivo",
            ),
            OutputLanguage::Arabic => text(
                "SumLeftStrictRightNonnegative",
                "الموجب + غير السالب > 0",
                "الموجب تمامًا زائد غير السالب موجب",
            ),
            OutputLanguage::Japanese => text(
                "SumLeftStrictRightNonnegative",
                "正数 + 非負数 > 0",
                "厳密な正数と非負数の和は正です",
            ),
            OutputLanguage::Korean => text(
                "SumLeftStrictRightNonnegative",
                "양수 + 비음수 > 0",
                "엄격한 양수와 비음수의 합은 양수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SumLeftStrictRightNonnegative",
                "Dương + không âm > 0",
                "Dương nghiêm ngặt cộng không âm là dương",
            ),
        }
    }
}

impl SumLeftNonnegativeRightStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "nonneg + pos > 0",
            "Nonnegative plus strictly positive is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SumLeftNonnegativeRightStrict",
            "非负 + 正 > 0",
            "非负加严格正为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SumLeftNonnegativeRightStrict",
                "非負數 + 正數 > 0",
                "非負數加嚴格正數為正",
            ),
            OutputLanguage::French => text(
                "SumLeftNonnegativeRightStrict",
                "Non-négatif + positif > 0",
                "Non-négatif plus strictement positif est positif",
            ),
            OutputLanguage::Russian => text(
                "SumLeftNonnegativeRightStrict",
                "Неотрицательное + положительное > 0",
                "Неотрицательное плюс строго положительное положительно",
            ),
            OutputLanguage::Spanish => text(
                "SumLeftNonnegativeRightStrict",
                "No negativo + positivo > 0",
                "No negativo más estrictamente positivo es positivo",
            ),
            OutputLanguage::Arabic => text(
                "SumLeftNonnegativeRightStrict",
                "غير السالب + الموجب > 0",
                "غير السالب زائد الموجب تمامًا موجب",
            ),
            OutputLanguage::Japanese => text(
                "SumLeftNonnegativeRightStrict",
                "非負数 + 正数 > 0",
                "非負数と厳密な正数の和は正です",
            ),
            OutputLanguage::Korean => text(
                "SumLeftNonnegativeRightStrict",
                "비음수 + 양수 > 0",
                "비음수와 엄격한 양수의 합은 양수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SumLeftNonnegativeRightStrict",
                "Không âm + dương > 0",
                "Không âm cộng dương nghiêm ngặt là dương",
            ),
        }
    }
}

impl ProductBothPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductBothPositive",
            "Product of positives > 0",
            "A product of positive factors is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductBothPositive", "正数积 > 0", "正因子之积为正")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ProductBothPositive", "正數乘積 > 0", "正因子的乘積為正")
            }
            OutputLanguage::French => text(
                "ProductBothPositive",
                "Produit de positifs > 0",
                "Un produit de facteurs positifs est positif",
            ),
            OutputLanguage::Russian => text(
                "ProductBothPositive",
                "Произведение положительных > 0",
                "Произведение положительных множителей положительно",
            ),
            OutputLanguage::Spanish => text(
                "ProductBothPositive",
                "Producto de positivos > 0",
                "Un producto de factores positivos es positivo",
            ),
            OutputLanguage::Arabic => text(
                "ProductBothPositive",
                "حاصل ضرب الموجبات > 0",
                "حاصل ضرب عوامل موجبة موجب",
            ),
            OutputLanguage::Japanese => text(
                "ProductBothPositive",
                "正数の積 > 0",
                "正の因子の積は正です",
            ),
            OutputLanguage::Korean => text(
                "ProductBothPositive",
                "양수의 곱 > 0",
                "양의 인자의 곱은 양수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ProductBothPositive",
                "Tích số dương > 0",
                "Tích các thừa số dương là dương",
            ),
        }
    }
}

impl EvenPowPositiveFromNonzeroBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "Even power > 0",
            "An even power of a checked nonzero real base is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EvenPowPositiveFromNonzero",
            "偶次幂 > 0",
            "已验证的非零实数底数的偶次幂为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "EvenPowPositiveFromNonzero",
                "偶數次方 > 0",
                "經驗證非零實數底數的偶數次方為正",
            ),
            OutputLanguage::French => text(
                "EvenPowPositiveFromNonzero",
                "Puissance paire > 0",
                "Une puissance paire d'une base réelle non nulle vérifiée est positive",
            ),
            OutputLanguage::Russian => text(
                "EvenPowPositiveFromNonzero",
                "Чётная степень > 0",
                "Чётная степень проверенного ненулевого вещественного основания положительна",
            ),
            OutputLanguage::Spanish => text(
                "EvenPowPositiveFromNonzero",
                "Potencia par > 0",
                "Una potencia par de base real no nula comprobada es positiva",
            ),
            OutputLanguage::Arabic => text(
                "EvenPowPositiveFromNonzero",
                "قوة زوجية > 0",
                "القوة الزوجية لأساس حقيقي غير صفري متحقق منه موجبة",
            ),
            OutputLanguage::Japanese => text(
                "EvenPowPositiveFromNonzero",
                "偶数乗 > 0",
                "検証済みの非ゼロ実数の底の偶数乗は正です",
            ),
            OutputLanguage::Korean => text(
                "EvenPowPositiveFromNonzero",
                "짝수 거듭제곱 > 0",
                "검증된 0이 아닌 실수 밑의 짝수 거듭제곱은 양수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "EvenPowPositiveFromNonzero",
                "Lũy thừa chẵn > 0",
                "Lũy thừa chẵn của cơ số thực khác không đã kiểm tra là dương",
            ),
        }
    }
}

impl PowPositiveFromPositiveBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "pow > 0 (pos base)",
            "A positive base raised to a real power is positive where defined",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowPositiveFromPositiveBase",
            "幂 > 0（正底）",
            "正底数的实数次幂在有定义时为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PowPositiveFromPositiveBase",
                "正底數的冪 > 0",
                "正底數的實數次方在定義成立時為正",
            ),
            OutputLanguage::French => text(
                "PowPositiveFromPositiveBase",
                "Puissance > 0 (base positive)",
                "Une base positive à une puissance réelle est positive là où elle est définie",
            ),
            OutputLanguage::Russian => text(
                "PowPositiveFromPositiveBase",
                "Степень > 0 (положительное основание)",
                "Положительное основание в вещественной степени положительно там, где определено",
            ),
            OutputLanguage::Spanish => text(
                "PowPositiveFromPositiveBase",
                "Potencia > 0 (base positiva)",
                "Una base positiva elevada a potencia real es positiva donde está definida",
            ),
            OutputLanguage::Arabic => text(
                "PowPositiveFromPositiveBase",
                "قوة > 0 (أساس موجب)",
                "الأساس الموجب مرفوعًا لقوة حقيقية موجب حيث يكون معرّفًا",
            ),
            OutputLanguage::Japanese => text(
                "PowPositiveFromPositiveBase",
                "冪 > 0（正の底）",
                "正の底の実数乗は定義されるところで正です",
            ),
            OutputLanguage::Korean => text(
                "PowPositiveFromPositiveBase",
                "거듭제곱 > 0(양수 밑)",
                "양의 밑의 실수 거듭제곱은 정의되는 곳에서 양수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PowPositiveFromPositiveBase",
                "Lũy thừa > 0 (cơ số dương)",
                "Cơ số dương nâng lũy thừa thực là dương khi xác định",
            ),
        }
    }
}

impl SqrtPositiveBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtPositive",
            "√ > 0",
            "Square root of a positive value is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtPositive", "√ > 0", "正数的平方根为正")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SqrtPositive", "√ > 0", "正值的平方根為正"),
            OutputLanguage::French => text(
                "SqrtPositive",
                "√ > 0",
                "La racine carrée d'un positif est positive",
            ),
            OutputLanguage::Russian => text(
                "SqrtPositive",
                "√ > 0",
                "Квадратный корень положительного значения положителен",
            ),
            OutputLanguage::Spanish => text(
                "SqrtPositive",
                "√ > 0",
                "La raíz cuadrada de un positivo es positiva",
            ),
            OutputLanguage::Arabic => {
                text("SqrtPositive", "√ > 0", "الجذر التربيعي لقيمة موجبة موجب")
            }
            OutputLanguage::Japanese => text("SqrtPositive", "√ > 0", "正の値の平方根は正です"),
            OutputLanguage::Korean => {
                text("SqrtPositive", "√ > 0", "양의 값의 제곱근은 양수입니다")
            }
            OutputLanguage::Vietnamese => text(
                "SqrtPositive",
                "√ > 0",
                "Căn bậc hai của giá trị dương là dương",
            ),
        }
    }
}

impl SqrtMonotoneIncreasingBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "√ monotone strict",
            "Square root is strictly increasing on [0,∞)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneIncreasing",
            "√ 严格单调",
            "平方根在 [0,∞) 上严格递增",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SqrtMonotoneIncreasing",
                "平方根嚴格單調性",
                "平方根在 [0,∞) 上嚴格遞增",
            ),
            OutputLanguage::French => text(
                "SqrtMonotoneIncreasing",
                "Monotonie stricte de √",
                "La racine carrée est strictement croissante sur [0,∞)",
            ),
            OutputLanguage::Russian => text(
                "SqrtMonotoneIncreasing",
                "Строгая монотонность √",
                "Квадратный корень строго возрастает на [0,∞)",
            ),
            OutputLanguage::Spanish => text(
                "SqrtMonotoneIncreasing",
                "Monotonía estricta de √",
                "La raíz cuadrada es estrictamente creciente en [0,∞)",
            ),
            OutputLanguage::Arabic => text(
                "SqrtMonotoneIncreasing",
                "رتابة صارمة لـ √",
                "الجذر التربيعي متزايد تمامًا على [0,∞)",
            ),
            OutputLanguage::Japanese => text(
                "SqrtMonotoneIncreasing",
                "√ の狭義単調性",
                "平方根は [0,∞) 上で狭義増加です",
            ),
            OutputLanguage::Korean => text(
                "SqrtMonotoneIncreasing",
                "√ 엄격한 단조성",
                "제곱근은 [0,∞)에서 엄격히 증가합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SqrtMonotoneIncreasing",
                "Đơn điệu nghiêm ngặt của √",
                "Căn bậc hai tăng nghiêm ngặt trên [0,∞)",
            ),
        }
    }
}

impl LogOrderPreservingStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "log order strict",
            "Log with base > 1 preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingStrict",
            "对数严格保序",
            "底大于 1 的对数保持严格序",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogOrderPreservingStrict",
                "對數嚴格序",
                "底數 > 1 的對數保持嚴格序",
            ),
            OutputLanguage::French => text(
                "LogOrderPreservingStrict",
                "Ordre strict du logarithme",
                "Le logarithme de base > 1 préserve l'ordre strict",
            ),
            OutputLanguage::Russian => text(
                "LogOrderPreservingStrict",
                "Строгий порядок логарифма",
                "Логарифм с основанием > 1 сохраняет строгий порядок",
            ),
            OutputLanguage::Spanish => text(
                "LogOrderPreservingStrict",
                "Orden estricto del logaritmo",
                "El logaritmo de base > 1 conserva el orden estricto",
            ),
            OutputLanguage::Arabic => text(
                "LogOrderPreservingStrict",
                "ترتيب صارم للوغاريتم",
                "اللوغاريتم بأساس > 1 يحفظ الترتيب الصارم",
            ),
            OutputLanguage::Japanese => text(
                "LogOrderPreservingStrict",
                "対数の狭義順序",
                "底 > 1 の対数は狭義順序を保ちます",
            ),
            OutputLanguage::Korean => text(
                "LogOrderPreservingStrict",
                "로그의 엄격한 순서",
                "밑 > 1인 로그는 엄격한 순서를 보존합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LogOrderPreservingStrict",
                "Thứ tự nghiêm ngặt của logarit",
                "Logarit cơ số > 1 bảo toàn thứ tự nghiêm ngặt",
            ),
        }
    }
}

impl LogPositiveFromBaseAndArgGtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "log > 0 when arg > 1",
            "Log with base > 1 is positive when the argument is > 1",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogPositiveFromBaseAndArgGtOne",
            "真数 > 1 时对数 > 0",
            "底大于 1 且真数大于 1 时对数为正",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "底數 > 1 的對數在引數 > 1 時為正",
            ),
            OutputLanguage::French => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "Le logarithme de base > 1 est positif si l'argument est > 1",
            ),
            OutputLanguage::Russian => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "Логарифм с основанием > 1 положителен при аргументе > 1",
            ),
            OutputLanguage::Spanish => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "El logaritmo de base > 1 es positivo si el argumento es > 1",
            ),
            OutputLanguage::Arabic => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "اللوغاريتم بأساس > 1 موجب إذا كان الوسيط > 1",
            ),
            OutputLanguage::Japanese => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "底 > 1 の対数は引数 > 1 の場合に正です",
            ),
            OutputLanguage::Korean => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "밑 > 1인 로그는 인수 > 1일 때 양수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LogPositiveFromBaseAndArgGtOne",
                "arg > 1 ⇒ log(arg)>0",
                "Logarit cơ số > 1 dương khi đối số > 1",
            ),
        }
    }
}

impl LogNegativeFromBaseGtOneArgInUnitIntervalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "log < 0 on (0,1)",
            "Log with base > 1 is negative on (0,1)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogNegativeFromBaseGtOneArgInUnitInterval",
            "对数在 (0,1) 上 < 0",
            "底大于 1 时对数在 (0,1) 上为负",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "底數 > 1 的對數在 (0,1) 上為負",
            ),
            OutputLanguage::French => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "Le logarithme de base > 1 est négatif sur (0,1)",
            ),
            OutputLanguage::Russian => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "Логарифм с основанием > 1 отрицателен на (0,1)",
            ),
            OutputLanguage::Spanish => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "El logaritmo de base > 1 es negativo en (0,1)",
            ),
            OutputLanguage::Arabic => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "اللوغاريتم بأساس > 1 سالب على (0,1)",
            ),
            OutputLanguage::Japanese => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "底 > 1 の対数は (0,1) 上で負です",
            ),
            OutputLanguage::Korean => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "밑 > 1인 로그는 (0,1)에서 음수입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LogNegativeFromBaseGtOneArgInUnitInterval",
                "x∈(0,1) ⇒ log(x)<0",
                "Logarit cơ số > 1 âm trên (0,1)",
            ),
        }
    }
}

impl LessTransitivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessTransitivity",
            "< transitivity",
            "Strict less is transitive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LessTransitivity", "< 传递性", "< 具有传递性")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LessTransitivity", "< 遞移性", "嚴格小於具遞移性")
            }
            OutputLanguage::French => text(
                "LessTransitivity",
                "Transitivité de <",
                "La relation strictement inférieure est transitive",
            ),
            OutputLanguage::Russian => text(
                "LessTransitivity",
                "Транзитивность <",
                "Строгое отношение меньше транзитивно",
            ),
            OutputLanguage::Spanish => text(
                "LessTransitivity",
                "Transitividad de <",
                "Menor estricto es transitivo",
            ),
            OutputLanguage::Arabic => {
                text("LessTransitivity", "تعدي <", "علاقة أصغر الصارمة متعدية")
            }
            OutputLanguage::Japanese => text(
                "LessTransitivity",
                "< の推移性",
                "狭義の小なり関係は推移的です",
            ),
            OutputLanguage::Korean => {
                text("LessTransitivity", "< 추이성", "엄격한 작음은 추이적입니다")
            }
            OutputLanguage::Vietnamese => text(
                "LessTransitivity",
                "Tính bắc cầu của <",
                "Nhỏ hơn nghiêm ngặt có tính bắc cầu",
            ),
        }
    }
}

impl LessFromPosDifferenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessFromPosDifference",
            "< from positive difference",
            "a < b when b-a is positive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LessFromPosDifference", "由正差得 <", "当 b-a 为正时 a < b")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LessFromPosDifference", "由差正得 <", "b-a > 0 ⇒ a < b")
            }
            OutputLanguage::French => text(
                "LessFromPosDifference",
                "< depuis une différence positive",
                "b-a > 0 ⇒ a < b",
            ),
            OutputLanguage::Russian => text(
                "LessFromPosDifference",
                "< из положительной разности",
                "b-a > 0 ⇒ a < b",
            ),
            OutputLanguage::Spanish => text(
                "LessFromPosDifference",
                "< desde diferencia positiva",
                "b-a > 0 ⇒ a < b",
            ),
            OutputLanguage::Arabic => {
                text("LessFromPosDifference", "< من فرق موجب", "b-a > 0 ⇒ a < b")
            }
            OutputLanguage::Japanese => {
                text("LessFromPosDifference", "正の差から <", "b-a > 0 ⇒ a < b")
            }
            OutputLanguage::Korean => {
                text("LessFromPosDifference", "양의 차로 <", "b-a > 0 ⇒ a < b")
            }
            OutputLanguage::Vietnamese => text(
                "LessFromPosDifference",
                "< từ hiệu dương",
                "b-a > 0 ⇒ a < b",
            ),
        }
    }
}

impl PosDifferenceFromLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "b-a > 0 from a < b",
            "Positive difference follows from <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PosDifferenceFromLess",
            "由 a < b 得 b-a > 0",
            "由 < 得到正差",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PosDifferenceFromLess", "a < b ⇒ b-a > 0", "< 推出差正")
            }
            OutputLanguage::French => text(
                "PosDifferenceFromLess",
                "a < b ⇒ b-a > 0",
                "Une différence positive découle de <",
            ),
            OutputLanguage::Russian => text(
                "PosDifferenceFromLess",
                "a < b ⇒ b-a > 0",
                "Положительная разность следует из <",
            ),
            OutputLanguage::Spanish => text(
                "PosDifferenceFromLess",
                "a < b ⇒ b-a > 0",
                "Una diferencia positiva se deduce de <",
            ),
            OutputLanguage::Arabic => text(
                "PosDifferenceFromLess",
                "a < b ⇒ b-a > 0",
                "ينتج الفرق الموجب من <",
            ),
            OutputLanguage::Japanese => text(
                "PosDifferenceFromLess",
                "a < b ⇒ b-a > 0",
                "< から差の正値性を導きます",
            ),
            OutputLanguage::Korean => text(
                "PosDifferenceFromLess",
                "a < b ⇒ b-a > 0",
                "<로 차의 양수성을 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PosDifferenceFromLess",
                "a < b ⇒ b-a > 0",
                "Hiệu dương suy ra từ <",
            ),
        }
    }
}

impl ModRemainderStrictUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "mod remainder < |mod|",
            "Euclidean remainder is strictly less than the modulus",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ModRemainderStrictUpperBound",
            "模余数 < |模|",
            "欧几里得余数严格小于模",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ModRemainderStrictUpperBound",
                "模餘數 < |模數|",
                "Euclid 餘數嚴格小於模數",
            ),
            OutputLanguage::French => text(
                "ModRemainderStrictUpperBound",
                "Reste modulaire < |module|",
                "Le reste euclidien est strictement inférieur au module",
            ),
            OutputLanguage::Russian => text(
                "ModRemainderStrictUpperBound",
                "Остаток < |модуль|",
                "Евклидов остаток строго меньше модуля",
            ),
            OutputLanguage::Spanish => text(
                "ModRemainderStrictUpperBound",
                "Resto modular < |módulo|",
                "El resto euclídeo es estrictamente menor que el módulo",
            ),
            OutputLanguage::Arabic => text(
                "ModRemainderStrictUpperBound",
                "باقي القسمة < |المقياس|",
                "الباقي الإقليدي أصغر تمامًا من المقياس",
            ),
            OutputLanguage::Japanese => text(
                "ModRemainderStrictUpperBound",
                "剰余 < |法|",
                "ユークリッドの剰余は法より厳密に小さいです",
            ),
            OutputLanguage::Korean => text(
                "ModRemainderStrictUpperBound",
                "나머지 < |법|",
                "유클리드 나머지는 법보다 엄격히 작습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ModRemainderStrictUpperBound",
                "Số dư < |môđun|",
                "Số dư Euclid nhỏ hơn môđun nghiêm ngặt",
            ),
        }
    }
}

impl DivMonotoneStrictSamePosDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "÷ monotone strict (pos)",
            "Division by the same positive divisor preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSamePosDivisor",
            "除法严格单调（正）",
            "同除以正除数保持严格序",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "DivMonotoneStrictSamePosDivisor",
                "正除數嚴格序單調性",
                "同除正數保持嚴格序",
            ),
            OutputLanguage::French => text(
                "DivMonotoneStrictSamePosDivisor",
                "Monotonie stricte avec diviseur positif",
                "Diviser par le même diviseur positif préserve l’ordre strict",
            ),
            OutputLanguage::Russian => text(
                "DivMonotoneStrictSamePosDivisor",
                "Строгая монотонность с положительным делителем",
                "Деление на один положительный делитель сохраняет строгий порядок",
            ),
            OutputLanguage::Spanish => text(
                "DivMonotoneStrictSamePosDivisor",
                "Monotonía estricta con divisor positivo",
                "Dividir por el mismo divisor positivo conserva el orden estricto",
            ),
            OutputLanguage::Arabic => text(
                "DivMonotoneStrictSamePosDivisor",
                "رتابة صارمة بمقسوم عليه موجب",
                "القسمة على المقسوم عليه الموجب نفسه تحفظ الترتيب الصارم",
            ),
            OutputLanguage::Japanese => text(
                "DivMonotoneStrictSamePosDivisor",
                "正の除数の狭義単調性",
                "同じ正の数で割ると狭義順序を保ちます",
            ),
            OutputLanguage::Korean => text(
                "DivMonotoneStrictSamePosDivisor",
                "양수 제수의 엄격한 단조성",
                "같은 양수로 나누면 엄격한 순서가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "DivMonotoneStrictSamePosDivisor",
                "Đơn điệu nghiêm ngặt với số chia dương",
                "Chia cùng số chia dương bảo toàn thứ tự nghiêm ngặt",
            ),
        }
    }
}

impl DivByGtOneLessSelfBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "÷(>1) < self",
            "Dividing by a number greater than one yields a strictly smaller positive value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivByGtOneLessSelf",
            "除以大于 1 小于自身",
            "除以大于 1 的数得到严格更小的正值",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "DivByGtOneLessSelf",
            "除以大於一的數使正值變小",
            "正值除以大於一的數得嚴格較小正值",
        )
    },
            OutputLanguage::French => {
        text(
            "DivByGtOneLessSelf",
            "Division par >1 diminue un positif",
            "Diviser une valeur positive par un nombre supérieur à un donne une valeur positive strictement inférieure",
        )
    },
            OutputLanguage::Russian => {
        text(
            "DivByGtOneLessSelf",
            "Деление на >1 уменьшает положительное",
            "Деление положительного значения на число больше единицы даёт строго меньшее положительное значение",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "DivByGtOneLessSelf",
            "Dividir por >1 reduce un positivo",
            "Dividir un valor positivo por un número mayor que uno da un valor positivo estrictamente menor",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "DivByGtOneLessSelf",
            "القسمة على >1 تصغّر القيمة الموجبة",
            "قسمة قيمة موجبة على عدد أكبر من واحد تعطي قيمة موجبة أصغر تمامًا",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "DivByGtOneLessSelf",
            "正値を >1 で割ると小さくなる",
            "正の値を一より大きい数で割ると厳密に小さい正の値になります",
        )
    },
            OutputLanguage::Korean => {
        text(
            "DivByGtOneLessSelf",
            "양수를 >1로 나누면 작아짐",
            "양의 값을 1보다 큰 수로 나누면 엄격히 작은 양의 값이 됩니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "DivByGtOneLessSelf",
            "Chia giá trị dương cho >1 cho giá trị nhỏ hơn",
            "Chia giá trị dương cho số lớn hơn một cho giá trị dương nhỏ hơn nghiêm ngặt",
        )
    },

        }
    }
}

impl DivMonotoneStrictSameNegDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "÷ monotone strict (neg)",
            "Division by the same negative divisor reverses and preserves strict order",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneStrictSameNegDivisor",
            "除法严格单调（负）",
            "同除以负除数反转并保持严格序",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "DivMonotoneStrictSameNegDivisor",
                "負除數嚴格序單調性",
                "同除負數反轉並保持嚴格序",
            ),
            OutputLanguage::French => text(
                "DivMonotoneStrictSameNegDivisor",
                "Monotonie stricte avec diviseur négatif",
                "Diviser par le même diviseur négatif inverse et préserve l’ordre strict",
            ),
            OutputLanguage::Russian => text(
                "DivMonotoneStrictSameNegDivisor",
                "Строгая монотонность с отрицательным делителем",
                "Деление на один отрицательный делитель обращает и сохраняет строгий порядок",
            ),
            OutputLanguage::Spanish => text(
                "DivMonotoneStrictSameNegDivisor",
                "Monotonía estricta con divisor negativo",
                "Dividir por el mismo divisor negativo invierte y conserva el orden estricto",
            ),
            OutputLanguage::Arabic => text(
                "DivMonotoneStrictSameNegDivisor",
                "رتابة صارمة بمقسوم عليه سالب",
                "القسمة على المقسوم عليه السالب نفسه تعكس وتحفظ الترتيب الصارم",
            ),
            OutputLanguage::Japanese => text(
                "DivMonotoneStrictSameNegDivisor",
                "負の除数の狭義単調性",
                "同じ負の数で割ると順序を反転して狭義順序を保ちます",
            ),
            OutputLanguage::Korean => text(
                "DivMonotoneStrictSameNegDivisor",
                "음수 제수의 엄격한 단조성",
                "같은 음수로 나누면 순서를 반전하고 엄격한 순서를 보존합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "DivMonotoneStrictSameNegDivisor",
                "Đơn điệu nghiêm ngặt với số chia âm",
                "Chia cùng số chia âm đảo chiều và bảo toàn thứ tự nghiêm ngặt",
            ),
        }
    }
}

impl NumericLowerBoundWeakenLtBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "Weaken numeric lower (<)",
            "A numeric lower bound weakens under <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLt",
            "放宽数值下界（<）",
            "数值下界在 < 下可放宽",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NumericLowerBoundWeakenLt",
                "放寬數值下界（<）",
                "數值下界依 < 放寬",
            ),
            OutputLanguage::French => text(
                "NumericLowerBoundWeakenLt",
                "Relâchement de borne inférieure (<)",
                "Une borne inférieure numérique se relâche sous <",
            ),
            OutputLanguage::Russian => text(
                "NumericLowerBoundWeakenLt",
                "Ослабление нижней границы (<)",
                "Числовая нижняя граница ослабляется по <",
            ),
            OutputLanguage::Spanish => text(
                "NumericLowerBoundWeakenLt",
                "Debilitar cota inferior (<)",
                "Una cota inferior numérica se debilita bajo <",
            ),
            OutputLanguage::Arabic => text(
                "NumericLowerBoundWeakenLt",
                "إضعاف الحد الأدنى (<)",
                "الحد الأدنى العددي يضعف تحت <",
            ),
            OutputLanguage::Japanese => text(
                "NumericLowerBoundWeakenLt",
                "数値下界の緩和（<）",
                "数値の下界を < で緩めます",
            ),
            OutputLanguage::Korean => text(
                "NumericLowerBoundWeakenLt",
                "수치 하한 완화 (<)",
                "수치 하한을 <로 완화합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NumericLowerBoundWeakenLt",
                "Nới cận dưới (<)",
                "Cận dưới số được nới theo <",
            ),
        }
    }
}

impl NumericUpperBoundWeakenLtBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "Weaken numeric upper (<)",
            "A numeric upper bound weakens under <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLt",
            "放宽数值上界（<）",
            "数值上界在 < 下可放宽",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NumericUpperBoundWeakenLt",
                "放寬數值上界（<）",
                "數值上界依 < 放寬",
            ),
            OutputLanguage::French => text(
                "NumericUpperBoundWeakenLt",
                "Relâchement de borne supérieure (<)",
                "Une borne supérieure numérique se relâche sous <",
            ),
            OutputLanguage::Russian => text(
                "NumericUpperBoundWeakenLt",
                "Ослабление верхней границы (<)",
                "Числовая верхняя граница ослабляется по <",
            ),
            OutputLanguage::Spanish => text(
                "NumericUpperBoundWeakenLt",
                "Debilitar cota superior (<)",
                "Una cota superior numérica se debilita bajo <",
            ),
            OutputLanguage::Arabic => text(
                "NumericUpperBoundWeakenLt",
                "إضعاف الحد الأعلى (<)",
                "الحد الأعلى العددي يضعف تحت <",
            ),
            OutputLanguage::Japanese => text(
                "NumericUpperBoundWeakenLt",
                "数値上界の緩和（<）",
                "数値の上界を < で緩めます",
            ),
            OutputLanguage::Korean => text(
                "NumericUpperBoundWeakenLt",
                "수치 상한 완화 (<)",
                "수치 상한을 <로 완화합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NumericUpperBoundWeakenLt",
                "Nới cận trên (<)",
                "Cận trên số được nới theo <",
            ),
        }
    }
}

impl PositiveEvenGtOneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PositiveEvenGtOne",
            "Positive even > 1",
            "A positive even integer is greater than one",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("PositiveEvenGtOne", "正偶数 > 1", "正偶数大于 1")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("PositiveEvenGtOne", "正偶數 > 1", "正偶整數大於一")
            }
            OutputLanguage::French => text(
                "PositiveEvenGtOne",
                "Pair positif > 1",
                "Un entier pair positif est supérieur à un",
            ),
            OutputLanguage::Russian => text(
                "PositiveEvenGtOne",
                "Положительное чётное > 1",
                "Положительное чётное целое больше единицы",
            ),
            OutputLanguage::Spanish => text(
                "PositiveEvenGtOne",
                "Par positivo > 1",
                "Un entero par positivo es mayor que uno",
            ),
            OutputLanguage::Arabic => text(
                "PositiveEvenGtOne",
                "زوجي موجب > 1",
                "العدد الصحيح الزوجي الموجب أكبر من واحد",
            ),
            OutputLanguage::Japanese => text(
                "PositiveEvenGtOne",
                "正の偶数 > 1",
                "正の偶整数は一より大きいです",
            ),
            OutputLanguage::Korean => text(
                "PositiveEvenGtOne",
                "양의 짝수 > 1",
                "양의 짝수 정수는 1보다 큽니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PositiveEvenGtOne",
                "Chẵn dương > 1",
                "Số nguyên chẵn dương lớn hơn một",
            ),
        }
    }
}

impl AddRightCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "Add right (<)",
            "Adding the same term on the right preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruenceStrict",
            "右边加（<）",
            "右边加上相同项保持 <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AddRightCongruenceStrict",
                "右加法（<）",
                "右加相同項保持 <",
            ),
            OutputLanguage::French => text(
                "AddRightCongruenceStrict",
                "Addition à droite (<)",
                "Ajouter le même terme à droite préserve <",
            ),
            OutputLanguage::Russian => text(
                "AddRightCongruenceStrict",
                "Сложение справа (<)",
                "Добавление одного члена справа сохраняет <",
            ),
            OutputLanguage::Spanish => text(
                "AddRightCongruenceStrict",
                "Suma derecha (<)",
                "Sumar el mismo término a la derecha conserva <",
            ),
            OutputLanguage::Arabic => text(
                "AddRightCongruenceStrict",
                "جمع أيمن (<)",
                "إضافة الحد نفسه يمينًا تحفظ <",
            ),
            OutputLanguage::Japanese => text(
                "AddRightCongruenceStrict",
                "右加算（<）",
                "右に同じ項を加えても < を保ちます",
            ),
            OutputLanguage::Korean => text(
                "AddRightCongruenceStrict",
                "오른쪽 덧셈 (<)",
                "오른쪽에 같은 항을 더하면 <가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AddRightCongruenceStrict",
                "Cộng phải (<)",
                "Cộng cùng hạng bên phải bảo toàn <",
            ),
        }
    }
}

impl AddLeftCongruenceStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "Add left (<)",
            "Adding the same term on the left preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruenceStrict",
            "左边加（<）",
            "左边加上相同项保持 <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AddLeftCongruenceStrict", "左加法（<）", "左加相同項保持 <")
            }
            OutputLanguage::French => text(
                "AddLeftCongruenceStrict",
                "Addition à gauche (<)",
                "Ajouter le même terme à gauche préserve <",
            ),
            OutputLanguage::Russian => text(
                "AddLeftCongruenceStrict",
                "Сложение слева (<)",
                "Добавление одного члена слева сохраняет <",
            ),
            OutputLanguage::Spanish => text(
                "AddLeftCongruenceStrict",
                "Suma izquierda (<)",
                "Sumar el mismo término a la izquierda conserva <",
            ),
            OutputLanguage::Arabic => text(
                "AddLeftCongruenceStrict",
                "جمع أيسر (<)",
                "إضافة الحد نفسه يسارًا تحفظ <",
            ),
            OutputLanguage::Japanese => text(
                "AddLeftCongruenceStrict",
                "左加算（<）",
                "左に同じ項を加えても < を保ちます",
            ),
            OutputLanguage::Korean => text(
                "AddLeftCongruenceStrict",
                "왼쪽 덧셈 (<)",
                "왼쪽에 같은 항을 더하면 <가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AddLeftCongruenceStrict",
                "Cộng trái (<)",
                "Cộng cùng hạng bên trái bảo toàn <",
            ),
        }
    }
}

impl MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "× left monotone (<)",
            "Multiplying on the left by a positive factor preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftPositiveMonotoneStrict",
            "左乘单调（<）",
            "左边乘以正因子保持 <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MulLeftPositiveMonotoneStrict",
                "左乘單調性（<）",
                "左乘正因子保持 <",
            ),
            OutputLanguage::French => text(
                "MulLeftPositiveMonotoneStrict",
                "Monotonie de multiplication gauche (<)",
                "Multiplier à gauche par un facteur positif préserve <",
            ),
            OutputLanguage::Russian => text(
                "MulLeftPositiveMonotoneStrict",
                "Монотонность умножения слева (<)",
                "Умножение слева на положительный множитель сохраняет <",
            ),
            OutputLanguage::Spanish => text(
                "MulLeftPositiveMonotoneStrict",
                "Monotonía de multiplicación izquierda (<)",
                "Multiplicar a la izquierda por factor positivo conserva <",
            ),
            OutputLanguage::Arabic => text(
                "MulLeftPositiveMonotoneStrict",
                "رتابة الضرب الأيسر (<)",
                "الضرب يسارًا بعامل موجب يحفظ <",
            ),
            OutputLanguage::Japanese => text(
                "MulLeftPositiveMonotoneStrict",
                "左乗算の単調性（<）",
                "左に正因子を掛けると < を保ちます",
            ),
            OutputLanguage::Korean => text(
                "MulLeftPositiveMonotoneStrict",
                "왼쪽 곱셈 단조성 (<)",
                "왼쪽에 양의 인자를 곱하면 <가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "MulLeftPositiveMonotoneStrict",
                "Đơn điệu nhân trái (<)",
                "Nhân bên trái với thừa số dương bảo toàn <",
            ),
        }
    }
}

impl MulRightPositiveMonotoneStrictBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "× right monotone (<)",
            "Multiplying on the right by a positive factor preserves <",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulRightPositiveMonotoneStrict",
            "右乘单调（<）",
            "右边乘以正因子保持 <",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MulRightPositiveMonotoneStrict",
                "右乘單調性（<）",
                "右乘正因子保持 <",
            ),
            OutputLanguage::French => text(
                "MulRightPositiveMonotoneStrict",
                "Monotonie de multiplication droite (<)",
                "Multiplier à droite par un facteur positif préserve <",
            ),
            OutputLanguage::Russian => text(
                "MulRightPositiveMonotoneStrict",
                "Монотонность умножения справа (<)",
                "Умножение справа на положительный множитель сохраняет <",
            ),
            OutputLanguage::Spanish => text(
                "MulRightPositiveMonotoneStrict",
                "Monotonía de multiplicación derecha (<)",
                "Multiplicar a la derecha por factor positivo conserva <",
            ),
            OutputLanguage::Arabic => text(
                "MulRightPositiveMonotoneStrict",
                "رتابة الضرب الأيمن (<)",
                "الضرب يمينًا بعامل موجب يحفظ <",
            ),
            OutputLanguage::Japanese => text(
                "MulRightPositiveMonotoneStrict",
                "右乗算の単調性（<）",
                "右に正因子を掛けると < を保ちます",
            ),
            OutputLanguage::Korean => text(
                "MulRightPositiveMonotoneStrict",
                "오른쪽 곱셈 단조성 (<)",
                "오른쪽에 양의 인자를 곱하면 <가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "MulRightPositiveMonotoneStrict",
                "Đơn điệu nhân phải (<)",
                "Nhân bên phải với thừa số dương bảo toàn <",
            ),
        }
    }
}

impl OrderSignFromPositiveLiteralBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "Sign from positive bound",
            "A positive literal bound forces the stated order/sign",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromPositiveLiteralBound",
            "由正下界得符号",
            "正的字面下界推出所述序/符号关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "OrderSignFromPositiveLiteralBound",
                "由正數界得符號",
                "正字面值界推出所述序或符號",
            ),
            OutputLanguage::French => text(
                "OrderSignFromPositiveLiteralBound",
                "Signe depuis une borne positive",
                "Une borne littérale positive impose l'ordre ou le signe indiqué",
            ),
            OutputLanguage::Russian => text(
                "OrderSignFromPositiveLiteralBound",
                "Знак из положительной границы",
                "Положительная литеральная граница задаёт указанный порядок или знак",
            ),
            OutputLanguage::Spanish => text(
                "OrderSignFromPositiveLiteralBound",
                "Signo desde cota positiva",
                "Una cota literal positiva fuerza el orden o signo indicado",
            ),
            OutputLanguage::Arabic => text(
                "OrderSignFromPositiveLiteralBound",
                "إشارة من حد موجب",
                "حد حرفي موجب يفرض الترتيب أو الإشارة المذكورة",
            ),
            OutputLanguage::Japanese => text(
                "OrderSignFromPositiveLiteralBound",
                "正の境界から符号",
                "正のリテラルの境界から指定された順序または符号を導きます",
            ),
            OutputLanguage::Korean => text(
                "OrderSignFromPositiveLiteralBound",
                "양수 경계로 부호",
                "양수 리터럴 경계로 명시된 순서 또는 부호를 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "OrderSignFromPositiveLiteralBound",
                "Dấu từ cận dương",
                "Cận literal dương suy ra thứ tự hoặc dấu đã nêu",
            ),
        }
    }
}

impl OrderFlipMulMinusOneToLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "Order flip by ×(-1)",
            "Multiplying by -1 reverses the inequality",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderFlipMulMinusOne",
            "乘以 -1 反转不等式",
            "两边同乘 -1 后不等式方向相反",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "OrderFlipMulMinusOne",
                "乘以 -1 反轉序",
                "乘以 -1 反轉不等式方向",
            ),
            OutputLanguage::French => text(
                "OrderFlipMulMinusOne",
                "Inversion d'ordre par ×(-1)",
                "Multiplier par -1 inverse l'inégalité",
            ),
            OutputLanguage::Russian => text(
                "OrderFlipMulMinusOne",
                "Обращение порядка при ×(-1)",
                "Умножение на -1 обращает неравенство",
            ),
            OutputLanguage::Spanish => text(
                "OrderFlipMulMinusOne",
                "Inversión de orden por ×(-1)",
                "Multiplicar por -1 invierte la desigualdad",
            ),
            OutputLanguage::Arabic => text(
                "OrderFlipMulMinusOne",
                "عكس الترتيب بالضرب في (-1)",
                "الضرب في -1 يعكس المتباينة",
            ),
            OutputLanguage::Japanese => text(
                "OrderFlipMulMinusOne",
                "×(-1) による順序反転",
                "-1 を掛けると不等号が反転します",
            ),
            OutputLanguage::Korean => text(
                "OrderFlipMulMinusOne",
                "×(-1)에 의한 순서 반전",
                "-1을 곱하면 부등호가 반전됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "OrderFlipMulMinusOne",
                "Đảo thứ tự bởi ×(-1)",
                "Nhân với -1 đảo chiều bất đẳng thức",
            ),
        }
    }
}

impl FromKnownGreaterBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FromKnownGreater",
                "Known converse order",
                "The opposite-direction comparison is already known",
            ),
            OutputLanguage::ChineseTraditional => {
                text("FromKnownGreater", "已知反向序關係", "反方向比較已知")
            }
            OutputLanguage::French => text(
                "FromKnownGreater",
                "Ordre inverse connu",
                "La comparaison dans le sens opposé est déjà connue",
            ),
            OutputLanguage::Russian => text(
                "FromKnownGreater",
                "Известный обратный порядок",
                "Сравнение в обратном направлении уже известно",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownGreater",
                "Orden inverso conocido",
                "La comparación en sentido opuesto ya es conocida",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownGreater",
                "ترتيب عكسي معلوم",
                "المقارنة في الاتجاه المعاكس معلومة بالفعل",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownGreater",
                "既知の逆向きの順序",
                "逆向きの比較は既知です",
            ),
            OutputLanguage::Korean => text(
                "FromKnownGreater",
                "알려진 역방향 순서",
                "반대 방향의 비교가 이미 알려져 있습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownGreater",
                "Thứ tự đảo chiều đã biết",
                "So sánh theo chiều ngược đã biết",
            ),

            OutputLanguage::Chinese => text(
                "FromKnownGreater",
                "已知反向序关系",
                "引用已知的反向比较事实",
            ),
        }
    }
}
