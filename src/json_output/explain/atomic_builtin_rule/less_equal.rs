//! Explain + cite for `LessEqualFactSearchProofByBuiltinRule`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{
    FromKnownGreaterEqualBuiltinRuleProof,
LessEqualFactSearchProofByBuiltinRule,
    AbsLeFromSymmetricBoundsBuiltinRuleProof,
    AbsLeImpliesNegUpperBuiltinRuleProof,
    AbsLeImpliesUpperBuiltinRuleProof,
    AbsNonnegativeBuiltinRuleProof,
    AbsReverseTriangleAddBuiltinRuleProof,
    AbsReverseTriangleSubBuiltinRuleProof,
    AbsSelfLowerBuiltinRuleProof,
    AbsSelfUpperBuiltinRuleProof,
    AbsTriangleInequalityBuiltinRuleProof,
    AddLeftCongruenceBuiltinRuleProof,
    AddLeftNonnegativeBuiltinRuleProof,
    AddRightCongruenceBuiltinRuleProof,
    AddRightNonnegativeBuiltinRuleProof,
    ArccosPrincipalLowerBoundBuiltinRuleProof,
    ArccosPrincipalUpperBoundBuiltinRuleProof,
    ArcsinPrincipalLowerBoundBuiltinRuleProof,
    ArcsinPrincipalUpperBoundBuiltinRuleProof,
    ClosedNumericComparisonBuiltinRuleProof,
    DivMonotoneWeakSameNegDivisorBuiltinRuleProof,
    DivMonotoneWeakSamePosDivisorBuiltinRuleProof,
    EvenPowNonnegativeBuiltinRuleProof,
    FiniteSetMaxMemberLeBuiltinRuleProof,
    PositiveCommonDivisorLeGcdBuiltinRuleProof,
    FiniteSetMinMemberLeBuiltinRuleProof,
    FiniteSetSizeAtLeastOneLeBuiltinRuleProof,
    FiniteSetSizeNonnegativeLeBuiltinRuleProof,
    FiniteSetSizeSubsetLeBuiltinRuleProof,
    FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof,
    FiniteSetSizeUnionLeSumBuiltinRuleProof,
    FromKnownInPositiveNaturalBuiltinRuleProof,
    FromKnownLessBuiltinRuleProof,
    IntegerAdjacencyLeBuiltinRuleProof,
    IntegerDiffAtLeastOneLeBuiltinRuleProof,
    IntegerPredecessorLeBuiltinRuleProof,
    IntegerSuccessorLeBuiltinRuleProof,
    LessEqualFromNonnegDifferenceBuiltinRuleProof,
    LessEqualFromPosDenomQuotientBoundBuiltinRuleProof,
    LessEqualFromPosDivProductBoundBuiltinRuleProof,
    LessEqualTransitivityBuiltinRuleProof,
    LogOrderPreservingWeakBuiltinRuleProof,
    ModRemainderNonnegativeBuiltinRuleProof,
    MulLeftNonnegativeMonotoneBuiltinRuleProof,
    MulRightNonnegativeMonotoneBuiltinRuleProof,
    NonnegDifferenceFromLessEqualBuiltinRuleProof,
    NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof,
    NumericLowerBoundWeakenLeBuiltinRuleProof,
    NumericUpperBoundWeakenLeBuiltinRuleProof,
    OrderReflexivityBuiltinRuleProof,
    PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof,
    PowNonnegFromPositiveBaseBuiltinRuleProof,
    ProductOfNonnegativesBuiltinRuleProof,
    SqrtMonotoneNondecreasingBuiltinRuleProof,
    SqrtNonnegativeBuiltinRuleProof,
    SubNonnegativeBuiltinRuleProof,
    SumOfNonnegativesBuiltinRuleProof,
    UnitCircleLowerBoundBuiltinRuleProof,
    UnitCircleUpperBoundBuiltinRuleProof
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToLessEqualBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_sign_from_literal_bound::OrderSignFromNegativeLiteralBoundBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl LessEqualFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => match lang {
                OutputLanguage::English => text("ClosedSubtractionBound", "Subtract from a stored numeric bound", "The stored upper or lower bound remains sufficient after subtracting the closed constant"),
                OutputLanguage::ChineseTraditional => text("ClosedSubtractionBound", "從已有數值界減去常數", "已有上界或下界減去封閉常數後仍足以滿足目標"),
                OutputLanguage::French => text("ClosedSubtractionBound", "Soustraction d'une borne numérique stockée", "La borne supérieure ou inférieure stockée reste suffisante après soustraction de la constante fermée"),
                OutputLanguage::Russian => text("ClosedSubtractionBound", "Вычитание из сохранённой числовой границы", "Сохранённая верхняя или нижняя граница остаётся достаточной после вычитания замкнутой константы"),
                OutputLanguage::Spanish => text("ClosedSubtractionBound", "Resta de una cota numérica almacenada", "La cota superior o inferior almacenada sigue siendo suficiente al restar la constante cerrada"),
                OutputLanguage::Arabic => text("ClosedSubtractionBound", "طرح من حد عددي مخزن", "يبقى الحد الأعلى أو الأدنى المخزن كافيًا بعد طرح الثابت المغلق"),
                OutputLanguage::Japanese => text("ClosedSubtractionBound", "保存済みの数値の境界からの減算", "保存済みの上界または下界は閉じた定数を引いた後も十分です"),
                OutputLanguage::Korean => text("ClosedSubtractionBound", "저장된 수치 경계에서 빼기", "저장된 상한 또는 하한은 닫힌 상수를 뺀 후에도 충분합니다"),
                OutputLanguage::Vietnamese => text("ClosedSubtractionBound", "Trừ từ cận số đã lưu", "Cận trên hoặc dưới đã lưu vẫn đủ sau khi trừ hằng đóng"),

                OutputLanguage::Chinese => text("ClosedSubtractionBound", "从已有数值界减去常数", "已有上界或下界减去闭式常数后满足目标弱序界"),
            },
            Self::ComplexModulusNonnegative => match lang {
                OutputLanguage::English => text("ComplexModulusNonnegative", "Nonnegative complex modulus", "The principal complex modulus is nonnegative"),
                OutputLanguage::ChineseTraditional => text("ComplexModulusNonnegative", "複數模長非負", "複數模長取非負主根"),
                OutputLanguage::French => text("ComplexModulusNonnegative", "Module complexe non négatif", "Le module complexe principal est non négatif"),
                OutputLanguage::Russian => text("ComplexModulusNonnegative", "Неотрицательный комплексный модуль", "Главный комплексный модуль неотрицателен"),
                OutputLanguage::Spanish => text("ComplexModulusNonnegative", "Módulo complejo no negativo", "El módulo complejo principal es no negativo"),
                OutputLanguage::Arabic => text("ComplexModulusNonnegative", "مقياس مركب غير سالب", "المقياس المركب الرئيسي غير سالب"),
                OutputLanguage::Japanese => text("ComplexModulusNonnegative", "複素数の絶対値の非負性", "複素数の主絶対値は非負です"),
                OutputLanguage::Korean => text("ComplexModulusNonnegative", "복소수 절댓값의 비음성", "복소수의 주 절댓값은 음이 아닙니다"),
                OutputLanguage::Vietnamese => text("ComplexModulusNonnegative", "Môđun phức không âm", "Môđun phức chính không âm"),

                OutputLanguage::Chinese => text("ComplexModulusNonnegative", "复数模长非负", "复数模长取非负主根"),
            },
            Self::FromKnownGreaterEqual(p) => p.rule_id_and_message(lang),
            Self::FromKnownOrderComplement(p) => p.rule_id_and_message(lang),
            Self::ClosedNumericComparison(p) => p.rule_id_and_message(lang),
            Self::OrderReflexivity(p) => p.rule_id_and_message(lang),
            Self::FromKnownLess(p) => p.rule_id_and_message(lang),
            Self::ArcsinPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArcsinPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::ArccosPrincipalLowerBound(p) => p.rule_id_and_message(lang),
            Self::ArccosPrincipalUpperBound(p) => p.rule_id_and_message(lang),
            Self::UnitCircleLowerBound(p) => p.rule_id_and_message(lang),
            Self::UnitCircleUpperBound(p) => p.rule_id_and_message(lang),
            Self::AbsNonnegative(p) => p.rule_id_and_message(lang),
            Self::AddRightNonnegative(p) => p.rule_id_and_message(lang),
            Self::AddLeftNonnegative(p) => p.rule_id_and_message(lang),
            Self::AddRightCongruence(p) => p.rule_id_and_message(lang),
            Self::AddLeftCongruence(p) => p.rule_id_and_message(lang),
            Self::SubNonnegative(p) => p.rule_id_and_message(lang),
            Self::MulLeftNonnegativeMonotone(p) => p.rule_id_and_message(lang),
            Self::MulRightNonnegativeMonotone(p) => p.rule_id_and_message(lang),
            Self::AbsLeFromSymmetricBounds(p) => p.rule_id_and_message(lang),
            Self::AbsLeImpliesUpper(p) => p.rule_id_and_message(lang),
            Self::AbsLeImpliesNegUpper(p) => p.rule_id_and_message(lang),
            Self::AbsSelfUpper(p) => p.rule_id_and_message(lang),
            Self::AbsSelfLower(p) => p.rule_id_and_message(lang),
            Self::AbsTriangleInequality(p) => p.rule_id_and_message(lang),
            Self::AbsReverseTriangleAdd(p) => p.rule_id_and_message(lang),
            Self::AbsReverseTriangleSub(p) => p.rule_id_and_message(lang),
            Self::SumOfNonnegatives(p) => p.rule_id_and_message(lang),
            Self::ProductOfNonnegatives(p) => p.rule_id_and_message(lang),
            Self::EvenPowNonnegative(p) => p.rule_id_and_message(lang),
            Self::PowNonnegFromPositiveBase(p) => p.rule_id_and_message(lang),
            Self::PowNonnegFromNonnegBasePosIntExp(p) => p.rule_id_and_message(lang),
            Self::SqrtNonnegative(p) => p.rule_id_and_message(lang),
            Self::SqrtMonotoneNondecreasing(p) => p.rule_id_and_message(lang),
            Self::FromKnownInPositiveNatural(p) => p.rule_id_and_message(lang),
            Self::LogOrderPreservingWeak(p) => p.rule_id_and_message(lang),
            Self::LessEqualTransitivity(p) => p.rule_id_and_message(lang),
            Self::LessEqualFromNonnegDifference(p) => p.rule_id_and_message(lang),
            Self::NonnegDifferenceFromLessEqual(p) => p.rule_id_and_message(lang),
            Self::ModRemainderNonnegative(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneWeakSamePosDivisor(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeNonnegativeLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeAtLeastOneLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeSubsetLe(p) => p.rule_id_and_message(lang),
            Self::DivMonotoneWeakSameNegDivisor(p) => p.rule_id_and_message(lang),
            Self::LessEqualFromPosDivProductBound(p) => p.rule_id_and_message(lang),
            Self::LessEqualFromPosDenomQuotientBound(p) => p.rule_id_and_message(lang),
            Self::NumericLowerBoundWeakenLe(p) => p.rule_id_and_message(lang),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => p.rule_id_and_message(lang),
            Self::NumericUpperBoundWeakenLe(p) => p.rule_id_and_message(lang),
            Self::IntegerSuccessorLe(p) => p.rule_id_and_message(lang),
            Self::IntegerAdjacencyLe(p) => p.rule_id_and_message(lang),
            Self::IntegerPredecessorLe(p) => p.rule_id_and_message(lang),
            Self::IntegerDiffAtLeastOneLe(p) => p.rule_id_and_message(lang),
            Self::PositiveCommonDivisorLeGcd(p) => p.rule_id_and_message(lang),
            Self::FiniteSetMaxMemberLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetMinMemberLe(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeUnionLeSum(p) => p.rule_id_and_message(lang),
            Self::FiniteSetSizeSurjectionCodomainLeDomain(p) => p.rule_id_and_message(lang),
            Self::OrderFlipMulMinusOne(p) => p.rule_id_and_message(lang),
            Self::OrderSignFromNegativeLiteralBound(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::ClosedSubtractionBound(p) => Some(p.bound.cite_fact_id),
            Self::FromKnownGreaterEqual(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownLess(p) => p.premise_proof.cite_fact_id(),
            Self::AbsLeImpliesUpper(p) => p.premise_proof.cite_fact_id(),
            Self::AbsLeImpliesNegUpper(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownInPositiveNatural(p) => p.premise_proof.cite_fact_id(),
            Self::LessEqualTransitivity(_) => None,
            Self::LessEqualFromNonnegDifference(p) => p.premise_proof.cite_fact_id(),
            Self::NonnegDifferenceFromLessEqual(p) => p.premise_proof.cite_fact_id(),
            Self::NumericLowerBoundWeakenLe(p) => Some(p.cite_fact_id),
            Self::NumericLowerBoundFromStrictPredecessorLe(p) => Some(p.cite_fact_id),
            Self::NumericUpperBoundWeakenLe(p) => Some(p.cite_fact_id),
            Self::OrderFlipMulMinusOne(p) => p.premise_proof.cite_fact_id(),
            Self::OrderSignFromNegativeLiteralBound(p) => Some(p.cite_fact_id),
            _ => None,
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

impl OrderReflexivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderReflexivity",
            "Order reflexivity",
            "A quantity is less-or-equal to itself",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderReflexivity",
            "序的自反性",
            "任何量都不大于也不小于自己（≤ 自身）",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("OrderReflexivity", "序關係自反性", "任一量小於或等於自身")
            }
            OutputLanguage::French => text(
                "OrderReflexivity",
                "Réflexivité de l'ordre",
                "Une quantité est inférieure ou égale à elle-même",
            ),
            OutputLanguage::Russian => text(
                "OrderReflexivity",
                "Рефлексивность порядка",
                "Величина меньше или равна самой себе",
            ),
            OutputLanguage::Spanish => text(
                "OrderReflexivity",
                "Reflexividad del orden",
                "Una cantidad es menor o igual a sí misma",
            ),
            OutputLanguage::Arabic => text(
                "OrderReflexivity",
                "انعكاسية الترتيب",
                "الكمية أصغر من نفسها أو تساويها",
            ),
            OutputLanguage::Japanese => {
                text("OrderReflexivity", "順序の反射性", "量は自身以下です")
            }
            OutputLanguage::Korean => text(
                "OrderReflexivity",
                "순서 반사성",
                "양은 자기 자신보다 작거나 같습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "OrderReflexivity",
                "Tính phản xạ của thứ tự",
                "Một đại lượng nhỏ hơn hoặc bằng chính nó",
            ),
        }
    }
}

impl FromKnownLessBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "From known less",
            "The weak order follows from a known strict less fact",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownLess",
            "已知严格小于",
            "弱序目标由已知的严格小于推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("FromKnownLess", "由已知小於", "弱序由已知嚴格小於命題得出")
            }
            OutputLanguage::French => text(
                "FromKnownLess",
                "Depuis une inégalité inférieure connue",
                "L'ordre large découle d'une inégalité stricte inférieure connue",
            ),
            OutputLanguage::Russian => text(
                "FromKnownLess",
                "Из известного меньшего значения",
                "Нестрогий порядок следует из известного строгого уменьшения",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownLess",
                "Desde desigualdad menor conocida",
                "El orden débil se deduce de desigualdad estricta menor conocida",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownLess",
                "من علاقة أصغر معلومة",
                "ينتج الترتيب غير الصارم من علاقة أصغر صارمة معلومة",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownLess",
                "既知の小なり関係から",
                "広義順序は既知の狭義の小なり命題から導かれます",
            ),
            OutputLanguage::Korean => text(
                "FromKnownLess",
                "알려진 작음 관계에서",
                "약한 순서는 알려진 엄격한 작음 명제에서 도출됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownLess",
                "Từ quan hệ nhỏ hơn đã biết",
                "Thứ tự không nghiêm ngặt suy ra từ quan hệ nhỏ hơn nghiêm ngặt đã biết",
            ),
        }
    }
}

impl ArcsinPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArcsinPrincipalLowerBound",
            "arcsin lower bound",
            "arcsin stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArcsinPrincipalLowerBound",
            "arcsin 下界",
            "arcsin 落在其主值下界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArcsinPrincipalLowerBound",
                "arcsin 下界",
                "arcsin 不低於主值下界",
            ),
            OutputLanguage::French => text(
                "ArcsinPrincipalLowerBound",
                "Borne inférieure de arcsin",
                "arcsin respecte sa borne principale inférieure",
            ),
            OutputLanguage::Russian => text(
                "ArcsinPrincipalLowerBound",
                "Нижняя граница arcsin",
                "arcsin не ниже своей главной нижней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArcsinPrincipalLowerBound",
                "Cota inferior de arcsin",
                "arcsin respeta su cota principal inferior",
            ),
            OutputLanguage::Arabic => text(
                "ArcsinPrincipalLowerBound",
                "حد أدنى لـ arcsin",
                "arcsin يبقى ضمن حده الرئيسي الأدنى",
            ),
            OutputLanguage::Japanese => text(
                "ArcsinPrincipalLowerBound",
                "arcsin の下界",
                "arcsin は主値の下界以上です",
            ),
            OutputLanguage::Korean => text(
                "ArcsinPrincipalLowerBound",
                "arcsin 하한",
                "arcsin는 주값 하한 이상입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArcsinPrincipalLowerBound",
                "Cận dưới arcsin",
                "arcsin giữ trong cận dưới chính",
            ),
        }
    }
}

impl ArcsinPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArcsinPrincipalUpperBound",
            "arcsin upper bound",
            "arcsin stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArcsinPrincipalUpperBound",
            "arcsin 上界",
            "arcsin 落在其主值上界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArcsinPrincipalUpperBound",
                "arcsin 上界",
                "arcsin 不高於主值上界",
            ),
            OutputLanguage::French => text(
                "ArcsinPrincipalUpperBound",
                "Borne supérieure de arcsin",
                "arcsin respecte sa borne principale supérieure",
            ),
            OutputLanguage::Russian => text(
                "ArcsinPrincipalUpperBound",
                "Верхняя граница arcsin",
                "arcsin не выше своей главной верхней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArcsinPrincipalUpperBound",
                "Cota superior de arcsin",
                "arcsin respeta su cota principal superior",
            ),
            OutputLanguage::Arabic => text(
                "ArcsinPrincipalUpperBound",
                "حد أعلى لـ arcsin",
                "arcsin يبقى ضمن حده الرئيسي الأعلى",
            ),
            OutputLanguage::Japanese => text(
                "ArcsinPrincipalUpperBound",
                "arcsin の上界",
                "arcsin は主値の上界以下です",
            ),
            OutputLanguage::Korean => text(
                "ArcsinPrincipalUpperBound",
                "arcsin 상한",
                "arcsin는 주값 상한 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArcsinPrincipalUpperBound",
                "Cận trên arcsin",
                "arcsin giữ trong cận trên chính",
            ),
        }
    }
}

impl ArccosPrincipalLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccosPrincipalLowerBound",
            "arccos lower bound",
            "arccos stays within its principal lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccosPrincipalLowerBound",
            "arccos 下界",
            "arccos 落在其主值下界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArccosPrincipalLowerBound",
                "arccos 下界",
                "arccos 不低於主值下界",
            ),
            OutputLanguage::French => text(
                "ArccosPrincipalLowerBound",
                "Borne inférieure de arccos",
                "arccos respecte sa borne principale inférieure",
            ),
            OutputLanguage::Russian => text(
                "ArccosPrincipalLowerBound",
                "Нижняя граница arccos",
                "arccos не ниже своей главной нижней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArccosPrincipalLowerBound",
                "Cota inferior de arccos",
                "arccos respeta su cota principal inferior",
            ),
            OutputLanguage::Arabic => text(
                "ArccosPrincipalLowerBound",
                "حد أدنى لـ arccos",
                "arccos يبقى ضمن حده الرئيسي الأدنى",
            ),
            OutputLanguage::Japanese => text(
                "ArccosPrincipalLowerBound",
                "arccos の下界",
                "arccos は主値の下界以上です",
            ),
            OutputLanguage::Korean => text(
                "ArccosPrincipalLowerBound",
                "arccos 하한",
                "arccos는 주값 하한 이상입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArccosPrincipalLowerBound",
                "Cận dưới arccos",
                "arccos giữ trong cận dưới chính",
            ),
        }
    }
}

impl ArccosPrincipalUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ArccosPrincipalUpperBound",
            "arccos upper bound",
            "arccos stays within its principal upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ArccosPrincipalUpperBound",
            "arccos 上界",
            "arccos 落在其主值上界内",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ArccosPrincipalUpperBound",
                "arccos 上界",
                "arccos 不高於主值上界",
            ),
            OutputLanguage::French => text(
                "ArccosPrincipalUpperBound",
                "Borne supérieure de arccos",
                "arccos respecte sa borne principale supérieure",
            ),
            OutputLanguage::Russian => text(
                "ArccosPrincipalUpperBound",
                "Верхняя граница arccos",
                "arccos не выше своей главной верхней границы",
            ),
            OutputLanguage::Spanish => text(
                "ArccosPrincipalUpperBound",
                "Cota superior de arccos",
                "arccos respeta su cota principal superior",
            ),
            OutputLanguage::Arabic => text(
                "ArccosPrincipalUpperBound",
                "حد أعلى لـ arccos",
                "arccos يبقى ضمن حده الرئيسي الأعلى",
            ),
            OutputLanguage::Japanese => text(
                "ArccosPrincipalUpperBound",
                "arccos の上界",
                "arccos は主値の上界以下です",
            ),
            OutputLanguage::Korean => text(
                "ArccosPrincipalUpperBound",
                "arccos 상한",
                "arccos는 주값 상한 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ArccosPrincipalUpperBound",
                "Cận trên arccos",
                "arccos giữ trong cận trên chính",
            ),
        }
    }
}

impl UnitCircleLowerBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnitCircleLowerBound",
            "Unit-circle lower bound",
            "Trig values on the unit circle respect the lower bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnitCircleLowerBound",
            "单位圆下界",
            "单位圆上的三角函数值满足下界",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("UnitCircleLowerBound", "單位圓下界", "單位圓三角值符合下界")
            }
            OutputLanguage::French => text(
                "UnitCircleLowerBound",
                "Borne inférieure du cercle unité",
                "Les valeurs trigonométriques sur le cercle unité respectent la borne inférieure",
            ),
            OutputLanguage::Russian => text(
                "UnitCircleLowerBound",
                "Нижняя граница единичной окружности",
                "Тригонометрические значения на единичной окружности соблюдают нижнюю границу",
            ),
            OutputLanguage::Spanish => text(
                "UnitCircleLowerBound",
                "Cota inferior del círculo unitario",
                "Los valores trigonométricos del círculo unitario respetan la cota inferior",
            ),
            OutputLanguage::Arabic => text(
                "UnitCircleLowerBound",
                "حد أدنى لدائرة الوحدة",
                "القيم المثلثية على دائرة الوحدة تحقق الحد الأدنى",
            ),
            OutputLanguage::Japanese => text(
                "UnitCircleLowerBound",
                "単位円の下界",
                "単位円上の三角関数値は下界を満たします",
            ),
            OutputLanguage::Korean => text(
                "UnitCircleLowerBound",
                "단위원 하한",
                "단위원의 삼각함숫값은 하한을 만족합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "UnitCircleLowerBound",
                "Cận dưới đường tròn đơn vị",
                "Giá trị lượng giác trên đường tròn đơn vị thỏa cận dưới",
            ),
        }
    }
}

impl UnitCircleUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnitCircleUpperBound",
            "Unit-circle upper bound",
            "Trig values on the unit circle respect the upper bound",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnitCircleUpperBound",
            "单位圆上界",
            "单位圆上的三角函数值满足上界",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("UnitCircleUpperBound", "單位圓上界", "單位圓三角值符合上界")
            }
            OutputLanguage::French => text(
                "UnitCircleUpperBound",
                "Borne supérieure du cercle unité",
                "Les valeurs trigonométriques sur le cercle unité respectent la borne supérieure",
            ),
            OutputLanguage::Russian => text(
                "UnitCircleUpperBound",
                "Верхняя граница единичной окружности",
                "Тригонометрические значения на единичной окружности соблюдают верхнюю границу",
            ),
            OutputLanguage::Spanish => text(
                "UnitCircleUpperBound",
                "Cota superior del círculo unitario",
                "Los valores trigonométricos del círculo unitario respetan la cota superior",
            ),
            OutputLanguage::Arabic => text(
                "UnitCircleUpperBound",
                "حد أعلى لدائرة الوحدة",
                "القيم المثلثية على دائرة الوحدة تحقق الحد الأعلى",
            ),
            OutputLanguage::Japanese => text(
                "UnitCircleUpperBound",
                "単位円の上界",
                "単位円上の三角関数値は上界を満たします",
            ),
            OutputLanguage::Korean => text(
                "UnitCircleUpperBound",
                "단위원 상한",
                "단위원의 삼각함숫값은 상한을 만족합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "UnitCircleUpperBound",
                "Cận trên đường tròn đơn vị",
                "Giá trị lượng giác trên đường tròn đơn vị thỏa cận trên",
            ),
        }
    }
}

impl AbsNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("AbsNonnegative", "|x| ≥ 0", "Absolute value is nonnegative")
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsNonnegative", "|x| ≥ 0", "绝对值非负")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("AbsNonnegative", "|x| ≥ 0", "絕對值非負"),
            OutputLanguage::French => text(
                "AbsNonnegative",
                "|x| ≥ 0",
                "La valeur absolue est non négative",
            ),
            OutputLanguage::Russian => text("AbsNonnegative", "|x| ≥ 0", "Модуль неотрицателен"),
            OutputLanguage::Spanish => text(
                "AbsNonnegative",
                "|x| ≥ 0",
                "El valor absoluto es no negativo",
            ),
            OutputLanguage::Arabic => text("AbsNonnegative", "|x| ≥ 0", "القيمة المطلقة غير سالبة"),
            OutputLanguage::Japanese => text("AbsNonnegative", "|x| ≥ 0", "絶対値は非負です"),
            OutputLanguage::Korean => text("AbsNonnegative", "|x| ≥ 0", "절댓값은 음이 아닙니다"),
            OutputLanguage::Vietnamese => {
                text("AbsNonnegative", "|x| ≥ 0", "Giá trị tuyệt đối không âm")
            }
        }
    }
}

impl AddRightNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddRightNonnegative",
            "Add right nonnegative",
            "Adding a nonnegative term on the right preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AddRightNonnegative", "右边加非负", "右边加上非负项保持 ≤")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AddRightNonnegative", "右加非負項", "右加非負項保持 ≤")
            }
            OutputLanguage::French => text(
                "AddRightNonnegative",
                "Addition non négative à droite",
                "Ajouter un terme non négatif à droite préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "AddRightNonnegative",
                "Неотрицательное сложение справа",
                "Добавление неотрицательного члена справа сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "AddRightNonnegative",
                "Suma no negativa derecha",
                "Sumar un término no negativo a la derecha conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "AddRightNonnegative",
                "جمع غير سالب أيمن",
                "إضافة حد غير سالب يمينًا تحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "AddRightNonnegative",
                "右に非負の項を加算",
                "右に非負の項を加えると ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "AddRightNonnegative",
                "오른쪽 비음수 덧셈",
                "오른쪽에 음이 아닌 항을 더하면 ≤가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AddRightNonnegative",
                "Cộng không âm bên phải",
                "Cộng hạng không âm bên phải bảo toàn ≤",
            ),
        }
    }
}

impl AddLeftNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddLeftNonnegative",
            "Add left nonnegative",
            "Adding a nonnegative term on the left preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AddLeftNonnegative", "左边加非负", "左边加上非负项保持 ≤")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AddLeftNonnegative", "左加非負項", "左加非負項保持 ≤")
            }
            OutputLanguage::French => text(
                "AddLeftNonnegative",
                "Addition non négative à gauche",
                "Ajouter un terme non négatif à gauche préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "AddLeftNonnegative",
                "Неотрицательное сложение слева",
                "Добавление неотрицательного члена слева сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "AddLeftNonnegative",
                "Suma no negativa izquierda",
                "Sumar un término no negativo a la izquierda conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "AddLeftNonnegative",
                "جمع غير سالب أيسر",
                "إضافة حد غير سالب يسارًا تحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "AddLeftNonnegative",
                "左に非負の項を加算",
                "左に非負の項を加えると ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "AddLeftNonnegative",
                "왼쪽 비음수 덧셈",
                "왼쪽에 음이 아닌 항을 더하면 ≤가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AddLeftNonnegative",
                "Cộng không âm bên trái",
                "Cộng hạng không âm bên trái bảo toàn ≤",
            ),
        }
    }
}

impl AddRightCongruenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddRightCongruence",
            "Add right (≤)",
            "Adding the same term on the right preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AddRightCongruence", "右边加（≤）", "右边加上相同项保持 ≤")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AddRightCongruence", "右加法（≤）", "右加相同項保持 ≤")
            }
            OutputLanguage::French => text(
                "AddRightCongruence",
                "Addition à droite (≤)",
                "Ajouter le même terme à droite préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "AddRightCongruence",
                "Сложение справа (≤)",
                "Добавление одного члена справа сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "AddRightCongruence",
                "Suma derecha (≤)",
                "Sumar el mismo término a la derecha conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "AddRightCongruence",
                "جمع أيمن (≤)",
                "إضافة الحد نفسه يمينًا تحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "AddRightCongruence",
                "右加算（≤）",
                "右に同じ項を加えても ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "AddRightCongruence",
                "오른쪽 덧셈 (≤)",
                "오른쪽에 같은 항을 더하면 ≤가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AddRightCongruence",
                "Cộng phải (≤)",
                "Cộng cùng hạng bên phải bảo toàn ≤",
            ),
        }
    }
}

impl AddLeftCongruenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AddLeftCongruence",
            "Add left (≤)",
            "Adding the same term on the left preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AddLeftCongruence", "左边加（≤）", "左边加上相同项保持 ≤")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AddLeftCongruence", "左加法（≤）", "左加相同項保持 ≤")
            }
            OutputLanguage::French => text(
                "AddLeftCongruence",
                "Addition à gauche (≤)",
                "Ajouter le même terme à gauche préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "AddLeftCongruence",
                "Сложение слева (≤)",
                "Добавление одного члена слева сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "AddLeftCongruence",
                "Suma izquierda (≤)",
                "Sumar el mismo término a la izquierda conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "AddLeftCongruence",
                "جمع أيسر (≤)",
                "إضافة الحد نفسه يسارًا تحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "AddLeftCongruence",
                "左加算（≤）",
                "左に同じ項を加えても ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "AddLeftCongruence",
                "왼쪽 덧셈 (≤)",
                "왼쪽에 같은 항을 더하면 ≤가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AddLeftCongruence",
                "Cộng trái (≤)",
                "Cộng cùng hạng bên trái bảo toàn ≤",
            ),
        }
    }
}

impl SubNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubNonnegative",
            "a-b ≥ 0",
            "A difference is nonnegative under the stated premises",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubNonnegative", "a-b ≥ 0", "在所述前提下差非负")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SubNonnegative", "a-b ≥ 0", "所述前提下差非負")
            }
            OutputLanguage::French => text(
                "SubNonnegative",
                "a-b ≥ 0",
                "Une différence est non négative sous les prémisses indiquées",
            ),
            OutputLanguage::Russian => text(
                "SubNonnegative",
                "a-b ≥ 0",
                "Разность неотрицательна при указанных предпосылках",
            ),
            OutputLanguage::Spanish => text(
                "SubNonnegative",
                "a-b ≥ 0",
                "Una diferencia es no negativa bajo las premisas indicadas",
            ),
            OutputLanguage::Arabic => text(
                "SubNonnegative",
                "a-b ≥ 0",
                "الفرق غير سالب تحت المقدمات المذكورة",
            ),
            OutputLanguage::Japanese => text(
                "SubNonnegative",
                "a-b ≥ 0",
                "指定された前提のもとで差は非負です",
            ),
            OutputLanguage::Korean => text(
                "SubNonnegative",
                "a-b ≥ 0",
                "명시된 전제에서 차는 음이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SubNonnegative",
                "a-b ≥ 0",
                "Hiệu không âm dưới các tiền đề đã nêu",
            ),
        }
    }
}

impl MulLeftNonnegativeMonotoneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulLeftNonnegativeMonotone",
            "× left monotone (≤)",
            "Multiplying on the left by a nonnegative factor preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulLeftNonnegativeMonotone",
            "左乘单调（≤）",
            "左边乘以非负因子保持 ≤",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MulLeftNonnegativeMonotone",
                "左乘單調性（≤）",
                "左乘非負因子保持 ≤",
            ),
            OutputLanguage::French => text(
                "MulLeftNonnegativeMonotone",
                "Monotonie de multiplication gauche (≤)",
                "Multiplier à gauche par un facteur non négatif préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "MulLeftNonnegativeMonotone",
                "Монотонность умножения слева (≤)",
                "Умножение слева на неотрицательный множитель сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "MulLeftNonnegativeMonotone",
                "Monotonía de multiplicación izquierda (≤)",
                "Multiplicar a la izquierda por factor no negativo conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "MulLeftNonnegativeMonotone",
                "رتابة الضرب الأيسر (≤)",
                "الضرب يسارًا بعامل غير سالب يحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "MulLeftNonnegativeMonotone",
                "左乗算の単調性（≤）",
                "左に非負因子を掛けると ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "MulLeftNonnegativeMonotone",
                "왼쪽 곱셈 단조성 (≤)",
                "왼쪽에 음이 아닌 인자를 곱하면 ≤가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "MulLeftNonnegativeMonotone",
                "Đơn điệu nhân trái (≤)",
                "Nhân bên trái với thừa số không âm bảo toàn ≤",
            ),
        }
    }
}

impl MulRightNonnegativeMonotoneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "MulRightNonnegativeMonotone",
            "× right monotone (≤)",
            "Multiplying on the right by a nonnegative factor preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "MulRightNonnegativeMonotone",
            "右乘单调（≤）",
            "右边乘以非负因子保持 ≤",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "MulRightNonnegativeMonotone",
                "右乘單調性（≤）",
                "右乘非負因子保持 ≤",
            ),
            OutputLanguage::French => text(
                "MulRightNonnegativeMonotone",
                "Monotonie de multiplication droite (≤)",
                "Multiplier à droite par un facteur non négatif préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "MulRightNonnegativeMonotone",
                "Монотонность умножения справа (≤)",
                "Умножение справа на неотрицательный множитель сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "MulRightNonnegativeMonotone",
                "Monotonía de multiplicación derecha (≤)",
                "Multiplicar a la derecha por factor no negativo conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "MulRightNonnegativeMonotone",
                "رتابة الضرب الأيمن (≤)",
                "الضرب يمينًا بعامل غير سالب يحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "MulRightNonnegativeMonotone",
                "右乗算の単調性（≤）",
                "右に非負因子を掛けると ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "MulRightNonnegativeMonotone",
                "오른쪽 곱셈 단조성 (≤)",
                "오른쪽에 음이 아닌 인자를 곱하면 ≤가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "MulRightNonnegativeMonotone",
                "Đơn điệu nhân phải (≤)",
                "Nhân bên phải với thừa số không âm bảo toàn ≤",
            ),
        }
    }
}

impl AbsLeFromSymmetricBoundsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsLeFromSymmetricBounds",
            "|x| ≤ M from ± bounds",
            "Absolute value is bounded by M when -M ≤ x ≤ M",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsLeFromSymmetricBounds",
            "由 ± 界得 |x| ≤ M",
            "当 -M ≤ x ≤ M 时，|x| ≤ M",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsLeFromSymmetricBounds",
                "由正負界得 |x| ≤ M",
                "當 -M ≤ x ≤ M，絕對值不大於 M",
            ),
            OutputLanguage::French => text(
                "AbsLeFromSymmetricBounds",
                "|x| ≤ M depuis les bornes ±",
                "La valeur absolue est bornée par M si -M ≤ x ≤ M",
            ),
            OutputLanguage::Russian => text(
                "AbsLeFromSymmetricBounds",
                "|x| ≤ M из границ ±",
                "Модуль ограничен M при -M ≤ x ≤ M",
            ),
            OutputLanguage::Spanish => text(
                "AbsLeFromSymmetricBounds",
                "|x| ≤ M desde cotas ±",
                "El valor absoluto está acotado por M si -M ≤ x ≤ M",
            ),
            OutputLanguage::Arabic => text(
                "AbsLeFromSymmetricBounds",
                "|x| ≤ M من حدود ±",
                "القيمة المطلقة محدودة بـ M عندما -M ≤ x ≤ M",
            ),
            OutputLanguage::Japanese => text(
                "AbsLeFromSymmetricBounds",
                "± の境界から |x| ≤ M",
                "-M ≤ x ≤ M の場合、絶対値は M 以下です",
            ),
            OutputLanguage::Korean => text(
                "AbsLeFromSymmetricBounds",
                "± 경계로 |x| ≤ M",
                "-M ≤ x ≤ M이면 절댓값은 M 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsLeFromSymmetricBounds",
                "|x| ≤ M từ cận ±",
                "Giá trị tuyệt đối bị chặn bởi M khi -M ≤ x ≤ M",
            ),
        }
    }
}

impl AbsLeImpliesUpperBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsLeImpliesUpper",
            "|x| ≤ M ⇒ x ≤ M",
            "An absolute-value upper bound implies the same bound on x",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsLeImpliesUpper",
            "|x| ≤ M ⇒ x ≤ M",
            "绝对值上界蕴含 x 的同样上界",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "絕對值上界同樣限制 x",
            ),
            OutputLanguage::French => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "Une borne supérieure de valeur absolue borne aussi x",
            ),
            OutputLanguage::Russian => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "Верхняя граница модуля также ограничивает x",
            ),
            OutputLanguage::Spanish => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "Una cota superior de valor absoluto también acota x",
            ),
            OutputLanguage::Arabic => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "الحد الأعلى للقيمة المطلقة يحد x أيضًا",
            ),
            OutputLanguage::Japanese => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "絶対値の上界は x にも同じ上界を与えます",
            ),
            OutputLanguage::Korean => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "절댓값 상한은 x에도 같은 상한을 줍니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsLeImpliesUpper",
                "|x| ≤ M ⇒ x ≤ M",
                "Cận trên giá trị tuyệt đối cũng chặn x",
            ),
        }
    }
}

impl AbsLeImpliesNegUpperBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsLeImpliesNegUpper",
            "|x| ≤ M ⇒ -x ≤ M",
            "An absolute-value upper bound implies the same bound on -x",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsLeImpliesNegUpper",
            "|x| ≤ M ⇒ -x ≤ M",
            "绝对值上界蕴含 -x 的同样上界",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "絕對值上界同樣限制 -x",
            ),
            OutputLanguage::French => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "Une borne supérieure de valeur absolue borne aussi -x",
            ),
            OutputLanguage::Russian => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "Верхняя граница модуля также ограничивает -x",
            ),
            OutputLanguage::Spanish => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "Una cota superior de valor absoluto también acota -x",
            ),
            OutputLanguage::Arabic => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "الحد الأعلى للقيمة المطلقة يحد -x أيضًا",
            ),
            OutputLanguage::Japanese => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "絶対値の上界は -x にも同じ上界を与えます",
            ),
            OutputLanguage::Korean => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "절댓값 상한은 -x에도 같은 상한을 줍니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsLeImpliesNegUpper",
                "|x| ≤ M ⇒ -x ≤ M",
                "Cận trên giá trị tuyệt đối cũng chặn -x",
            ),
        }
    }
}

impl AbsSelfUpperBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsSelfUpper",
            "x ≤ |x|",
            "A quantity is at most its absolute value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsSelfUpper", "x ≤ |x|", "任何量都不大于其绝对值")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AbsSelfUpper", "x ≤ |x|", "任一量至多為其絕對值")
            }
            OutputLanguage::French => text(
                "AbsSelfUpper",
                "x ≤ |x|",
                "Une quantité est au plus sa valeur absolue",
            ),
            OutputLanguage::Russian => text(
                "AbsSelfUpper",
                "x ≤ |x|",
                "Величина не больше своего модуля",
            ),
            OutputLanguage::Spanish => text(
                "AbsSelfUpper",
                "x ≤ |x|",
                "Una cantidad es como máximo su valor absoluto",
            ),
            OutputLanguage::Arabic => text(
                "AbsSelfUpper",
                "x ≤ |x|",
                "الكمية لا تزيد على قيمتها المطلقة",
            ),
            OutputLanguage::Japanese => text("AbsSelfUpper", "x ≤ |x|", "量はその絶対値以下です"),
            OutputLanguage::Korean => {
                text("AbsSelfUpper", "x ≤ |x|", "양은 자기 절댓값 이하입니다")
            }
            OutputLanguage::Vietnamese => text(
                "AbsSelfUpper",
                "x ≤ |x|",
                "Một đại lượng không vượt quá giá trị tuyệt đối của nó",
            ),
        }
    }
}

impl AbsSelfLowerBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsSelfLower",
            "-|x| ≤ x",
            "A quantity is at least the negation of its absolute value",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsSelfLower", "-|x| ≤ x", "任何量都不小于其绝对值的相反数")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AbsSelfLower", "-|x| ≤ x", "任一量至少為其絕對值的相反數")
            }
            OutputLanguage::French => text(
                "AbsSelfLower",
                "-|x| ≤ x",
                "Une quantité est au moins l'opposé de sa valeur absolue",
            ),
            OutputLanguage::Russian => text(
                "AbsSelfLower",
                "-|x| ≤ x",
                "Величина не меньше отрицания своего модуля",
            ),
            OutputLanguage::Spanish => text(
                "AbsSelfLower",
                "-|x| ≤ x",
                "Una cantidad es al menos el negativo de su valor absoluto",
            ),
            OutputLanguage::Arabic => text(
                "AbsSelfLower",
                "-|x| ≤ x",
                "الكمية لا تقل عن سالب قيمتها المطلقة",
            ),
            OutputLanguage::Japanese => {
                text("AbsSelfLower", "-|x| ≤ x", "量はその絶対値の負値以上です")
            }
            OutputLanguage::Korean => text(
                "AbsSelfLower",
                "-|x| ≤ x",
                "양은 자기 절댓값의 음수 이상입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsSelfLower",
                "-|x| ≤ x",
                "Một đại lượng ít nhất bằng số đối của giá trị tuyệt đối của nó",
            ),
        }
    }
}

impl AbsTriangleInequalityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsTriangleInequality",
            "Triangle inequality",
            "|a+b| ≤ |a|+|b|",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("AbsTriangleInequality", "三角不等式", "|a+b| ≤ |a|+|b|")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("AbsTriangleInequality", "三角不等式", "|a+b| ≤ |a|+|b|")
            }
            OutputLanguage::French => text(
                "AbsTriangleInequality",
                "Inégalité triangulaire",
                "|a+b| ≤ |a|+|b|",
            ),
            OutputLanguage::Russian => text(
                "AbsTriangleInequality",
                "Неравенство треугольника",
                "|a+b| ≤ |a|+|b|",
            ),
            OutputLanguage::Spanish => text(
                "AbsTriangleInequality",
                "Desigualdad triangular",
                "|a+b| ≤ |a|+|b|",
            ),
            OutputLanguage::Arabic => {
                text("AbsTriangleInequality", "متباينة المثلث", "|a+b| ≤ |a|+|b|")
            }
            OutputLanguage::Japanese => {
                text("AbsTriangleInequality", "三角不等式", "|a+b| ≤ |a|+|b|")
            }
            OutputLanguage::Korean => {
                text("AbsTriangleInequality", "삼각부등식", "|a+b| ≤ |a|+|b|")
            }
            OutputLanguage::Vietnamese => text(
                "AbsTriangleInequality",
                "Bất đẳng thức tam giác",
                "|a+b| ≤ |a|+|b|",
            ),
        }
    }
}

impl AbsReverseTriangleAddBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsReverseTriangleAdd",
            "Reverse triangle (|a|+|b|)",
            "Reverse triangle inequality for absolute values of a sum",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsReverseTriangleAdd",
            "反向三角（|a|+|b|）",
            "和的绝对值的反向三角不等式",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsReverseTriangleAdd",
                "反三角不等式（|a|+|b|）",
                "和的絕對值反三角不等式",
            ),
            OutputLanguage::French => text(
                "AbsReverseTriangleAdd",
                "Triangle inverse (|a|+|b|)",
                "Inégalité triangulaire inverse pour la valeur absolue d'une somme",
            ),
            OutputLanguage::Russian => text(
                "AbsReverseTriangleAdd",
                "Обратный треугольник (|a|+|b|)",
                "Обратное неравенство треугольника для модуля суммы",
            ),
            OutputLanguage::Spanish => text(
                "AbsReverseTriangleAdd",
                "Triángulo inverso (|a|+|b|)",
                "Desigualdad triangular inversa para valor absoluto de suma",
            ),
            OutputLanguage::Arabic => text(
                "AbsReverseTriangleAdd",
                "مثلث عكسي (|a|+|b|)",
                "متباينة المثلث العكسية للقيمة المطلقة للمجموع",
            ),
            OutputLanguage::Japanese => text(
                "AbsReverseTriangleAdd",
                "逆三角不等式（|a|+|b|）",
                "和の絶対値の逆三角不等式",
            ),
            OutputLanguage::Korean => text(
                "AbsReverseTriangleAdd",
                "역삼각부등식 (|a|+|b|)",
                "합의 절댓값 역삼각부등식",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsReverseTriangleAdd",
                "Tam giác đảo (|a|+|b|)",
                "Bất đẳng thức tam giác đảo cho giá trị tuyệt đối của tổng",
            ),
        }
    }
}

impl AbsReverseTriangleSubBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "AbsReverseTriangleSub",
            "Reverse triangle (|a|-|b|)",
            "Reverse triangle inequality for absolute values of a difference",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "AbsReverseTriangleSub",
            "反向三角（|a|-|b|）",
            "差的绝对值的反向三角不等式",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "AbsReverseTriangleSub",
                "反三角不等式（|a|-|b|）",
                "差的絕對值反三角不等式",
            ),
            OutputLanguage::French => text(
                "AbsReverseTriangleSub",
                "Triangle inverse (|a|-|b|)",
                "Inégalité triangulaire inverse pour la valeur absolue d'une différence",
            ),
            OutputLanguage::Russian => text(
                "AbsReverseTriangleSub",
                "Обратный треугольник (|a|-|b|)",
                "Обратное неравенство треугольника для модуля разности",
            ),
            OutputLanguage::Spanish => text(
                "AbsReverseTriangleSub",
                "Triángulo inverso (|a|-|b|)",
                "Desigualdad triangular inversa para valor absoluto de diferencia",
            ),
            OutputLanguage::Arabic => text(
                "AbsReverseTriangleSub",
                "مثلث عكسي (|a|-|b|)",
                "متباينة المثلث العكسية للقيمة المطلقة للفرق",
            ),
            OutputLanguage::Japanese => text(
                "AbsReverseTriangleSub",
                "逆三角不等式（|a|-|b|）",
                "差の絶対値の逆三角不等式",
            ),
            OutputLanguage::Korean => text(
                "AbsReverseTriangleSub",
                "역삼각부등식 (|a|-|b|)",
                "차의 절댓값 역삼각부등식",
            ),
            OutputLanguage::Vietnamese => text(
                "AbsReverseTriangleSub",
                "Tam giác đảo (|a|-|b|)",
                "Bất đẳng thức tam giác đảo cho giá trị tuyệt đối của hiệu",
            ),
        }
    }
}

impl SumOfNonnegativesBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SumOfNonnegatives",
            "Sum of nonnegatives ≥ 0",
            "A sum of nonnegative terms is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SumOfNonnegatives", "非负和 ≥ 0", "非负项之和非负")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("SumOfNonnegatives", "非負數和 ≥ 0", "非負項的和非負")
            }
            OutputLanguage::French => text(
                "SumOfNonnegatives",
                "Somme de non-négatifs ≥ 0",
                "Une somme de termes non négatifs est non négative",
            ),
            OutputLanguage::Russian => text(
                "SumOfNonnegatives",
                "Сумма неотрицательных ≥ 0",
                "Сумма неотрицательных членов неотрицательна",
            ),
            OutputLanguage::Spanish => text(
                "SumOfNonnegatives",
                "Suma de no negativos ≥ 0",
                "Una suma de términos no negativos es no negativa",
            ),
            OutputLanguage::Arabic => text(
                "SumOfNonnegatives",
                "مجموع غير السوالب ≥ 0",
                "مجموع حدود غير سالبة غير سالب",
            ),
            OutputLanguage::Japanese => text(
                "SumOfNonnegatives",
                "非負数の和 ≥ 0",
                "非負の項の和は非負です",
            ),
            OutputLanguage::Korean => text(
                "SumOfNonnegatives",
                "비음수의 합 ≥ 0",
                "음이 아닌 항의 합은 음이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SumOfNonnegatives",
                "Tổng số không âm ≥ 0",
                "Tổng các hạng không âm không âm",
            ),
        }
    }
}

impl ProductOfNonnegativesBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ProductOfNonnegatives",
            "Product of nonnegatives ≥ 0",
            "A product of nonnegative factors is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ProductOfNonnegatives", "非负积 ≥ 0", "非负因子之积非负")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ProductOfNonnegatives",
                "非負數乘積 ≥ 0",
                "非負因子的乘積非負",
            ),
            OutputLanguage::French => text(
                "ProductOfNonnegatives",
                "Produit de non-négatifs ≥ 0",
                "Un produit de facteurs non négatifs est non négatif",
            ),
            OutputLanguage::Russian => text(
                "ProductOfNonnegatives",
                "Произведение неотрицательных ≥ 0",
                "Произведение неотрицательных множителей неотрицательно",
            ),
            OutputLanguage::Spanish => text(
                "ProductOfNonnegatives",
                "Producto de no negativos ≥ 0",
                "Un producto de factores no negativos es no negativo",
            ),
            OutputLanguage::Arabic => text(
                "ProductOfNonnegatives",
                "حاصل ضرب غير السوالب ≥ 0",
                "حاصل ضرب عوامل غير سالبة غير سالب",
            ),
            OutputLanguage::Japanese => text(
                "ProductOfNonnegatives",
                "非負数の積 ≥ 0",
                "非負因子の積は非負です",
            ),
            OutputLanguage::Korean => text(
                "ProductOfNonnegatives",
                "비음수의 곱 ≥ 0",
                "음이 아닌 인자의 곱은 음이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ProductOfNonnegatives",
                "Tích số không âm ≥ 0",
                "Tích các thừa số không âm không âm",
            ),
        }
    }
}

impl EvenPowNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "EvenPowNonnegative",
            "Even power ≥ 0",
            "An even power of a checked real base is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "EvenPowNonnegative",
            "偶次幂 ≥ 0",
            "已验证的实数底数的偶次幂非负",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "EvenPowNonnegative",
                "偶數次方 ≥ 0",
                "經驗證實數底數的偶數次方非負",
            ),
            OutputLanguage::French => text(
                "EvenPowNonnegative",
                "Puissance paire ≥ 0",
                "Une puissance paire d'une base réelle vérifiée est non négative",
            ),
            OutputLanguage::Russian => text(
                "EvenPowNonnegative",
                "Чётная степень ≥ 0",
                "Чётная степень проверенного вещественного основания неотрицательна",
            ),
            OutputLanguage::Spanish => text(
                "EvenPowNonnegative",
                "Potencia par ≥ 0",
                "Una potencia par de base real comprobada es no negativa",
            ),
            OutputLanguage::Arabic => text(
                "EvenPowNonnegative",
                "قوة زوجية ≥ 0",
                "القوة الزوجية لأساس حقيقي متحقق منه غير سالبة",
            ),
            OutputLanguage::Japanese => text(
                "EvenPowNonnegative",
                "偶数乗 ≥ 0",
                "検証済みの実数の底の偶数乗は非負です",
            ),
            OutputLanguage::Korean => text(
                "EvenPowNonnegative",
                "짝수 거듭제곱 ≥ 0",
                "검증된 실수 밑의 짝수 거듭제곱은 음이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "EvenPowNonnegative",
                "Lũy thừa chẵn ≥ 0",
                "Lũy thừa chẵn của cơ số thực đã kiểm tra không âm",
            ),
        }
    }
}

impl PowNonnegFromPositiveBaseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowNonnegFromPositiveBase",
            "pow ≥ 0 (pos base)",
            "A positive base raised to a real power is nonnegative where defined",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowNonnegFromPositiveBase",
            "幂 ≥ 0（正底）",
            "正底数的实数次幂在有定义时非负",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PowNonnegFromPositiveBase",
                "正底數的冪 ≥ 0",
                "正底數的實數次方在定義成立時非負",
            ),
            OutputLanguage::French => text(
                "PowNonnegFromPositiveBase",
                "Puissance ≥ 0 (base positive)",
                "Une base positive à une puissance réelle est non négative là où elle est définie",
            ),
            OutputLanguage::Russian => text(
                "PowNonnegFromPositiveBase",
                "Степень ≥ 0 (положительное основание)",
                "Положительное основание в вещественной степени неотрицательно там, где определено",
            ),
            OutputLanguage::Spanish => text(
                "PowNonnegFromPositiveBase",
                "Potencia ≥ 0 (base positiva)",
                "Una base positiva elevada a potencia real es no negativa donde está definida",
            ),
            OutputLanguage::Arabic => text(
                "PowNonnegFromPositiveBase",
                "قوة ≥ 0 (أساس موجب)",
                "الأساس الموجب مرفوعًا لقوة حقيقية غير سالب حيث يكون معرّفًا",
            ),
            OutputLanguage::Japanese => text(
                "PowNonnegFromPositiveBase",
                "冪 ≥ 0（正の底）",
                "正の底の実数乗は定義されるところで非負です",
            ),
            OutputLanguage::Korean => text(
                "PowNonnegFromPositiveBase",
                "거듭제곱 ≥ 0(양수 밑)",
                "양의 밑의 실수 거듭제곱은 정의되는 곳에서 음이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PowNonnegFromPositiveBase",
                "Lũy thừa ≥ 0 (cơ số dương)",
                "Cơ số dương nâng lũy thừa thực không âm khi xác định",
            ),
        }
    }
}

impl PowNonnegFromNonnegBasePosIntExpBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "PowNonnegFromNonnegBasePosIntExp",
            "pow ≥ 0 (nonneg base)",
            "A nonnegative base to a positive integer power is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "PowNonnegFromNonnegBasePosIntExp",
            "幂 ≥ 0（非负底）",
            "非负底数的正整数次幂非负",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "非負底數的冪 ≥ 0",
                "非負底數的正整數次方非負",
            ),
            OutputLanguage::French => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "Puissance ≥ 0 (base non négative)",
                "Une base non négative à une puissance entière positive est non négative",
            ),
            OutputLanguage::Russian => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "Степень ≥ 0 (неотрицательное основание)",
                "Неотрицательное основание в положительной целой степени неотрицательно",
            ),
            OutputLanguage::Spanish => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "Potencia ≥ 0 (base no negativa)",
                "Una base no negativa elevada a potencia entera positiva es no negativa",
            ),
            OutputLanguage::Arabic => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "قوة ≥ 0 (أساس غير سالب)",
                "الأساس غير السالب مرفوعًا لقوة صحيحة موجبة غير سالب",
            ),
            OutputLanguage::Japanese => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "冪 ≥ 0（非負の底）",
                "非負の底の正の整数乗は非負です",
            ),
            OutputLanguage::Korean => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "거듭제곱 ≥ 0(비음수 밑)",
                "음이 아닌 밑의 양의 정수 거듭제곱은 음이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "PowNonnegFromNonnegBasePosIntExp",
                "Lũy thừa ≥ 0 (cơ số không âm)",
                "Cơ số không âm nâng lũy thừa nguyên dương không âm",
            ),
        }
    }
}

impl SqrtNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text("SqrtNonnegative", "√ ≥ 0", "Square root is nonnegative")
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SqrtNonnegative", "√ ≥ 0", "平方根非负")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text("SqrtNonnegative", "√ ≥ 0", "平方根非負"),
            OutputLanguage::French => text(
                "SqrtNonnegative",
                "√ ≥ 0",
                "La racine carrée est non négative",
            ),
            OutputLanguage::Russian => text(
                "SqrtNonnegative",
                "√ ≥ 0",
                "Квадратный корень неотрицателен",
            ),
            OutputLanguage::Spanish => text(
                "SqrtNonnegative",
                "√ ≥ 0",
                "La raíz cuadrada es no negativa",
            ),
            OutputLanguage::Arabic => text("SqrtNonnegative", "√ ≥ 0", "الجذر التربيعي غير سالب"),
            OutputLanguage::Japanese => text("SqrtNonnegative", "√ ≥ 0", "平方根は非負です"),
            OutputLanguage::Korean => text("SqrtNonnegative", "√ ≥ 0", "제곱근은 음이 아닙니다"),
            OutputLanguage::Vietnamese => text("SqrtNonnegative", "√ ≥ 0", "Căn bậc hai không âm"),
        }
    }
}

impl SqrtMonotoneNondecreasingBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneNondecreasing",
            "√ monotone weak",
            "Square root is nondecreasing on [0,∞)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SqrtMonotoneNondecreasing",
            "√ 弱单调",
            "平方根在 [0,∞) 上非减",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SqrtMonotoneNondecreasing",
                "平方根弱單調性",
                "平方根在 [0,∞) 上非遞減",
            ),
            OutputLanguage::French => text(
                "SqrtMonotoneNondecreasing",
                "Monotonie large de √",
                "La racine carrée est croissante au sens large sur [0,∞)",
            ),
            OutputLanguage::Russian => text(
                "SqrtMonotoneNondecreasing",
                "Нестрогая монотонность √",
                "Квадратный корень не убывает на [0,∞)",
            ),
            OutputLanguage::Spanish => text(
                "SqrtMonotoneNondecreasing",
                "Monotonía débil de √",
                "La raíz cuadrada es no decreciente en [0,∞)",
            ),
            OutputLanguage::Arabic => text(
                "SqrtMonotoneNondecreasing",
                "رتابة غير صارمة لـ √",
                "الجذر التربيعي غير متناقص على [0,∞)",
            ),
            OutputLanguage::Japanese => text(
                "SqrtMonotoneNondecreasing",
                "√ の広義単調性",
                "平方根は [0,∞) 上で非減少です",
            ),
            OutputLanguage::Korean => text(
                "SqrtMonotoneNondecreasing",
                "√ 약한 단조성",
                "제곱근은 [0,∞)에서 감소하지 않습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SqrtMonotoneNondecreasing",
                "Đơn điệu không nghiêm ngặt của √",
                "Căn bậc hai không giảm trên [0,∞)",
            ),
        }
    }
}

impl FromKnownInPositiveNaturalBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FromKnownInPositiveNatural",
            "From known in positive N",
            "The goal follows from a known positive-natural membership",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FromKnownInPositiveNatural",
            "已知属于正自然数",
            "目标由已知的正自然数成员关系推出",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FromKnownInPositiveNatural",
                "由已知正自然數成員",
                "目標由已知正自然數成員關係得出",
            ),
            OutputLanguage::French => text(
                "FromKnownInPositiveNatural",
                "Depuis une appartenance connue aux naturels positifs",
                "L'objectif découle d'une appartenance connue aux naturels positifs",
            ),
            OutputLanguage::Russian => text(
                "FromKnownInPositiveNatural",
                "Из известной принадлежности положительным натуральным",
                "Цель следует из известной принадлежности положительным натуральным",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownInPositiveNatural",
                "Desde pertenencia conocida a naturales positivos",
                "El objetivo se deduce de pertenencia conocida a naturales positivos",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownInPositiveNatural",
                "من انتماء معلوم للأعداد الطبيعية الموجبة",
                "ينتج الهدف من انتماء معلوم للأعداد الطبيعية الموجبة",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownInPositiveNatural",
                "既知の正の自然数への所属から",
                "目標は既知の正の自然数への所属から導かれます",
            ),
            OutputLanguage::Korean => text(
                "FromKnownInPositiveNatural",
                "알려진 양의 자연수 소속에서",
                "목표는 알려진 양의 자연수 소속에서 도출됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownInPositiveNatural",
                "Từ sự thuộc về số tự nhiên dương đã biết",
                "Mục tiêu suy ra từ sự thuộc về số tự nhiên dương đã biết",
            ),
        }
    }
}

impl LogOrderPreservingWeakBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingWeak",
            "log order weak",
            "Log with base > 1 preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LogOrderPreservingWeak",
            "对数弱保序",
            "底大于 1 的对数保持 ≤",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LogOrderPreservingWeak",
                "對數弱序",
                "底數 > 1 的對數保持 ≤",
            ),
            OutputLanguage::French => text(
                "LogOrderPreservingWeak",
                "Ordre large du logarithme",
                "Le logarithme de base > 1 préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "LogOrderPreservingWeak",
                "Нестрогий порядок логарифма",
                "Логарифм с основанием > 1 сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "LogOrderPreservingWeak",
                "Orden débil del logaritmo",
                "El logaritmo de base > 1 conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "LogOrderPreservingWeak",
                "ترتيب غير صارم للوغاريتم",
                "اللوغاريتم بأساس > 1 يحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "LogOrderPreservingWeak",
                "対数の広義順序",
                "底 > 1 の対数は ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "LogOrderPreservingWeak",
                "로그의 약한 순서",
                "밑 > 1인 로그는 ≤를 보존합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LogOrderPreservingWeak",
                "Thứ tự không nghiêm ngặt của logarit",
                "Logarit cơ số > 1 bảo toàn ≤",
            ),
        }
    }
}

impl LessEqualTransitivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessEqualTransitivity",
            "≤ transitivity",
            "Less-or-equal is transitive",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("LessEqualTransitivity", "≤ 传递性", "≤ 具有传递性")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("LessEqualTransitivity", "≤ 遞移性", "小於或等於具遞移性")
            }
            OutputLanguage::French => text(
                "LessEqualTransitivity",
                "Transitivité de ≤",
                "La relation inférieure ou égale est transitive",
            ),
            OutputLanguage::Russian => text(
                "LessEqualTransitivity",
                "Транзитивность ≤",
                "Отношение меньше или равно транзитивно",
            ),
            OutputLanguage::Spanish => text(
                "LessEqualTransitivity",
                "Transitividad de ≤",
                "Menor o igual es transitivo",
            ),
            OutputLanguage::Arabic => text(
                "LessEqualTransitivity",
                "تعدي ≤",
                "علاقة أصغر أو يساوي متعدية",
            ),
            OutputLanguage::Japanese => text(
                "LessEqualTransitivity",
                "≤ の推移性",
                "以下の関係は推移的です",
            ),
            OutputLanguage::Korean => text(
                "LessEqualTransitivity",
                "≤ 추이성",
                "작거나 같음은 추이적입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LessEqualTransitivity",
                "Tính bắc cầu của ≤",
                "Quan hệ nhỏ hơn hoặc bằng có tính bắc cầu",
            ),
        }
    }
}

impl LessEqualFromNonnegDifferenceBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromNonnegDifference",
            "≤ from nonnegative difference",
            "a ≤ b when b-a is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromNonnegDifference",
            "由非负差得 ≤",
            "当 b-a 非负时 a ≤ b",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LessEqualFromNonnegDifference",
                "由差非負得 ≤",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
            OutputLanguage::French => text(
                "LessEqualFromNonnegDifference",
                "≤ depuis une différence non négative",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
            OutputLanguage::Russian => text(
                "LessEqualFromNonnegDifference",
                "≤ из неотрицательной разности",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
            OutputLanguage::Spanish => text(
                "LessEqualFromNonnegDifference",
                "≤ desde diferencia no negativa",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
            OutputLanguage::Arabic => text(
                "LessEqualFromNonnegDifference",
                "≤ من فرق غير سالب",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
            OutputLanguage::Japanese => text(
                "LessEqualFromNonnegDifference",
                "非負の差から ≤",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
            OutputLanguage::Korean => text(
                "LessEqualFromNonnegDifference",
                "음이 아닌 차로 ≤",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
            OutputLanguage::Vietnamese => text(
                "LessEqualFromNonnegDifference",
                "≤ từ hiệu không âm",
                "b-a ≥ 0 ⇒ a ≤ b",
            ),
        }
    }
}

impl NonnegDifferenceFromLessEqualBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NonnegDifferenceFromLessEqual",
            "b-a ≥ 0 from a ≤ b",
            "Nonnegative difference follows from ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NonnegDifferenceFromLessEqual",
            "由 a ≤ b 得 b-a ≥ 0",
            "由 ≤ 得到非负差",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "≤ 推出差非負",
            ),
            OutputLanguage::French => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "Une différence non négative découle de ≤",
            ),
            OutputLanguage::Russian => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "Неотрицательная разность следует из ≤",
            ),
            OutputLanguage::Spanish => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "Una diferencia no negativa se deduce de ≤",
            ),
            OutputLanguage::Arabic => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "ينتج الفرق غير السالب من ≤",
            ),
            OutputLanguage::Japanese => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "≤ から差の非負性を導きます",
            ),
            OutputLanguage::Korean => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "≤로 차의 비음성을 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NonnegDifferenceFromLessEqual",
                "a ≤ b ⇒ b-a ≥ 0",
                "Hiệu không âm suy ra từ ≤",
            ),
        }
    }
}

impl ModRemainderNonnegativeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ModRemainderNonnegative",
            "mod remainder ≥ 0",
            "Euclidean remainder is nonnegative",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("ModRemainderNonnegative", "模余数 ≥ 0", "欧几里得余数非负")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("ModRemainderNonnegative", "模餘數 ≥ 0", "Euclid 餘數非負")
            }
            OutputLanguage::French => text(
                "ModRemainderNonnegative",
                "Reste modulaire ≥ 0",
                "Le reste euclidien est non négatif",
            ),
            OutputLanguage::Russian => text(
                "ModRemainderNonnegative",
                "Остаток по модулю ≥ 0",
                "Евклидов остаток неотрицателен",
            ),
            OutputLanguage::Spanish => text(
                "ModRemainderNonnegative",
                "Resto modular ≥ 0",
                "El resto euclídeo es no negativo",
            ),
            OutputLanguage::Arabic => text(
                "ModRemainderNonnegative",
                "باقي القسمة ≥ 0",
                "الباقي الإقليدي غير سالب",
            ),
            OutputLanguage::Japanese => text(
                "ModRemainderNonnegative",
                "剰余 ≥ 0",
                "ユークリッドの剰余は非負です",
            ),
            OutputLanguage::Korean => text(
                "ModRemainderNonnegative",
                "나머지 ≥ 0",
                "유클리드 나머지는 음이 아닙니다",
            ),
            OutputLanguage::Vietnamese => text(
                "ModRemainderNonnegative",
                "Số dư ≥ 0",
                "Số dư Euclid không âm",
            ),
        }
    }
}

impl DivMonotoneWeakSamePosDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneWeakSamePosDivisor",
            "÷ monotone weak (pos)",
            "Division by the same positive divisor preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneWeakSamePosDivisor",
            "除法弱单调（正）",
            "同除以正除数保持 ≤",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "DivMonotoneWeakSamePosDivisor",
                "正除數弱序單調性",
                "同除正數保持 ≤",
            ),
            OutputLanguage::French => text(
                "DivMonotoneWeakSamePosDivisor",
                "Monotonie large avec diviseur positif",
                "Diviser par le même diviseur positif préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "DivMonotoneWeakSamePosDivisor",
                "Нестрогая монотонность с положительным делителем",
                "Деление на один положительный делитель сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "DivMonotoneWeakSamePosDivisor",
                "Monotonía débil con divisor positivo",
                "Dividir por el mismo divisor positivo conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "DivMonotoneWeakSamePosDivisor",
                "رتابة غير صارمة بمقسوم عليه موجب",
                "القسمة على المقسوم عليه الموجب نفسه تحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "DivMonotoneWeakSamePosDivisor",
                "正の除数の広義単調性",
                "同じ正の数で割ると ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "DivMonotoneWeakSamePosDivisor",
                "양수 제수의 약한 단조성",
                "같은 양수로 나누면 ≤가 보존됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "DivMonotoneWeakSamePosDivisor",
                "Đơn điệu không nghiêm ngặt với số chia dương",
                "Chia cùng số chia dương bảo toàn ≤",
            ),
        }
    }
}

impl FiniteSetSizeNonnegativeLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeNonnegativeLe",
            "|S| ≥ 0 as ≤",
            "Finite-set size is nonnegative (as ≤)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeNonnegativeLe",
            "|S| ≥ 0（≤）",
            "有限集大小非负（写成 ≤）",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "有限集合大小非負（以 ≤ 表示）",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "La taille d'un ensemble fini est non négative (avec ≤)",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "Размер конечного множества неотрицателен (через ≤)",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "El tamaño del conjunto finito es no negativo (con ≤)",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "حجم المجموعة المنتهية غير سالب (بصيغة ≤)",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "有限集合の大きさは非負です（≤ 形式）",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "유한 집합의 크기는 음이 아닙니다(≤ 형식)",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeNonnegativeLe",
                "0 ≤ |S|",
                "Kích thước tập hữu hạn không âm (dạng ≤)",
            ),
        }
    }
}

impl FiniteSetSizeAtLeastOneLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeAtLeastOneLe",
            "|S| ≥ 1 as ≤",
            "A nonempty finite set has size at least one (as ≤)",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeAtLeastOneLe",
            "|S| ≥ 1（≤）",
            "非空有限集大小至少为 1（写成 ≤）",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "非空有限集合的大小至少為一（以 ≤ 表示）",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "Un ensemble fini non vide a au moins un élément (avec ≤)",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "Непустое конечное множество имеет размер не меньше одного (через ≤)",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "Un conjunto finito no vacío tiene tamaño al menos uno (con ≤)",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "المجموعة المنتهية غير الخالية لها عنصر واحد على الأقل (بصيغة ≤)",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "空でない有限集合の大きさは少なくとも一です（≤ 形式）",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "비어 있지 않은 유한 집합의 크기는 적어도 1입니다(≤ 형식)",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeAtLeastOneLe",
                "1 ≤ |S|",
                "Tập hữu hạn không rỗng có kích thước ít nhất một (dạng ≤)",
            ),
        }
    }
}

impl FiniteSetSizeSubsetLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSubsetLe",
            "|A| ≤ |B| from A⊆B",
            "Subset relation implies a weak inequality on finite-set sizes",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSubsetLe",
            "由 A⊆B 得 |A| ≤ |B|",
            "子集关系蕴含有限集大小的弱不等式",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "子集關係推出有限集合大小的弱不等式",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "L'inclusion implique une inégalité large sur les tailles finies",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "Включение даёт нестрогое неравенство размеров конечных множеств",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "La inclusión implica desigualdad débil de tamaños finitos",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "الاحتواء الجزئي يستلزم متباينة غير صارمة لأحجام المجموعات المنتهية",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "包含関係から有限集合の大きさの広義不等式を導きます",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "부분집합 관계로 유한 집합 크기의 약한 부등식을 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeSubsetLe",
                "A⊆B ⇒ |A| ≤ |B|",
                "Quan hệ tập con suy ra bất đẳng thức không nghiêm ngặt về kích thước hữu hạn",
            ),
        }
    }
}

impl DivMonotoneWeakSameNegDivisorBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneWeakSameNegDivisor",
            "÷ monotone weak (neg)",
            "Division by the same negative divisor reverses and preserves ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "DivMonotoneWeakSameNegDivisor",
            "除法弱单调（负）",
            "同除以负除数反转并保持 ≤",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "DivMonotoneWeakSameNegDivisor",
                "負除數弱序單調性",
                "同除負數反轉並保持 ≤",
            ),
            OutputLanguage::French => text(
                "DivMonotoneWeakSameNegDivisor",
                "Monotonie large avec diviseur négatif",
                "Diviser par le même diviseur négatif inverse et préserve ≤",
            ),
            OutputLanguage::Russian => text(
                "DivMonotoneWeakSameNegDivisor",
                "Нестрогая монотонность с отрицательным делителем",
                "Деление на один отрицательный делитель обращает и сохраняет ≤",
            ),
            OutputLanguage::Spanish => text(
                "DivMonotoneWeakSameNegDivisor",
                "Monotonía débil con divisor negativo",
                "Dividir por el mismo divisor negativo invierte y conserva ≤",
            ),
            OutputLanguage::Arabic => text(
                "DivMonotoneWeakSameNegDivisor",
                "رتابة غير صارمة بمقسوم عليه سالب",
                "القسمة على المقسوم عليه السالب نفسه تعكس وتحفظ ≤",
            ),
            OutputLanguage::Japanese => text(
                "DivMonotoneWeakSameNegDivisor",
                "負の除数の広義単調性",
                "同じ負の数で割ると順序を反転して ≤ を保ちます",
            ),
            OutputLanguage::Korean => text(
                "DivMonotoneWeakSameNegDivisor",
                "음수 제수의 약한 단조성",
                "같은 음수로 나누면 순서를 반전하고 ≤를 보존합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "DivMonotoneWeakSameNegDivisor",
                "Đơn điệu không nghiêm ngặt với số chia âm",
                "Chia cùng số chia âm đảo chiều và bảo toàn ≤",
            ),
        }
    }
}

impl LessEqualFromPosDivProductBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromPosDivProductBound",
            "≤ from positive divisor product",
            "A product bound with positive divisor yields ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromPosDivProductBound",
            "由正除数积得 ≤",
            "正除数的积界给出 ≤",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LessEqualFromPosDivProductBound",
                "由正除數乘積得 ≤",
                "正除數的乘積界得 ≤",
            ),
            OutputLanguage::French => text(
                "LessEqualFromPosDivProductBound",
                "≤ depuis produit à diviseur positif",
                "Une borne de produit avec diviseur positif donne ≤",
            ),
            OutputLanguage::Russian => text(
                "LessEqualFromPosDivProductBound",
                "≤ из произведения с положительным делителем",
                "Граница произведения с положительным делителем даёт ≤",
            ),
            OutputLanguage::Spanish => text(
                "LessEqualFromPosDivProductBound",
                "≤ desde producto con divisor positivo",
                "Una cota de producto con divisor positivo da ≤",
            ),
            OutputLanguage::Arabic => text(
                "LessEqualFromPosDivProductBound",
                "≤ من حاصل ضرب بمقسوم عليه موجب",
                "حد حاصل ضرب مع مقسوم عليه موجب يعطي ≤",
            ),
            OutputLanguage::Japanese => text(
                "LessEqualFromPosDivProductBound",
                "正の除数の積から ≤",
                "正の除数を伴う積の境界から ≤ を導きます",
            ),
            OutputLanguage::Korean => text(
                "LessEqualFromPosDivProductBound",
                "양의 제수 곱으로 ≤",
                "양의 제수가 있는 곱의 경계로 ≤를 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LessEqualFromPosDivProductBound",
                "≤ từ tích với số chia dương",
                "Cận tích với số chia dương suy ra ≤",
            ),
        }
    }
}

impl LessEqualFromPosDenomQuotientBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromPosDenomQuotientBound",
            "≤ from positive-denom quotient",
            "A quotient bound with positive denominator yields ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "LessEqualFromPosDenomQuotientBound",
            "由正分母商得 ≤",
            "正分母的商界给出 ≤",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "LessEqualFromPosDenomQuotientBound",
                "由正分母商得 ≤",
                "正分母的商界得 ≤",
            ),
            OutputLanguage::French => text(
                "LessEqualFromPosDenomQuotientBound",
                "≤ depuis quotient à dénominateur positif",
                "Une borne de quotient à dénominateur positif donne ≤",
            ),
            OutputLanguage::Russian => text(
                "LessEqualFromPosDenomQuotientBound",
                "≤ из частного с положительным знаменателем",
                "Граница частного с положительным знаменателем даёт ≤",
            ),
            OutputLanguage::Spanish => text(
                "LessEqualFromPosDenomQuotientBound",
                "≤ desde cociente con denominador positivo",
                "Una cota de cociente con denominador positivo da ≤",
            ),
            OutputLanguage::Arabic => text(
                "LessEqualFromPosDenomQuotientBound",
                "≤ من خارج قسمة بمقام موجب",
                "حد خارج قسمة بمقام موجب يعطي ≤",
            ),
            OutputLanguage::Japanese => text(
                "LessEqualFromPosDenomQuotientBound",
                "正の分母の商から ≤",
                "正の分母を伴う商の境界から ≤ を導きます",
            ),
            OutputLanguage::Korean => text(
                "LessEqualFromPosDenomQuotientBound",
                "양의 분모 몫으로 ≤",
                "양의 분모가 있는 몫의 경계로 ≤를 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "LessEqualFromPosDenomQuotientBound",
                "≤ từ thương có mẫu dương",
                "Cận thương với mẫu dương suy ra ≤",
            ),
        }
    }
}

impl NumericLowerBoundWeakenLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLe",
            "Weaken numeric lower (≤)",
            "A numeric lower bound weakens under ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundWeakenLe",
            "放宽数值下界（≤）",
            "数值下界在 ≤ 下可放宽",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NumericLowerBoundWeakenLe",
                "放寬數值下界（≤）",
                "數值下界依 ≤ 放寬",
            ),
            OutputLanguage::French => text(
                "NumericLowerBoundWeakenLe",
                "Relâchement de borne inférieure (≤)",
                "Une borne inférieure numérique se relâche sous ≤",
            ),
            OutputLanguage::Russian => text(
                "NumericLowerBoundWeakenLe",
                "Ослабление нижней границы (≤)",
                "Числовая нижняя граница ослабляется по ≤",
            ),
            OutputLanguage::Spanish => text(
                "NumericLowerBoundWeakenLe",
                "Debilitar cota inferior (≤)",
                "Una cota inferior numérica se debilita bajo ≤",
            ),
            OutputLanguage::Arabic => text(
                "NumericLowerBoundWeakenLe",
                "إضعاف الحد الأدنى (≤)",
                "الحد الأدنى العددي يضعف تحت ≤",
            ),
            OutputLanguage::Japanese => text(
                "NumericLowerBoundWeakenLe",
                "数値下界の緩和（≤）",
                "数値の下界を ≤ で緩めます",
            ),
            OutputLanguage::Korean => text(
                "NumericLowerBoundWeakenLe",
                "수치 하한 완화 (≤)",
                "수치 하한을 ≤로 완화합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NumericLowerBoundWeakenLe",
                "Nới cận dưới (≤)",
                "Cận dưới số được nới theo ≤",
            ),
        }
    }
}

impl NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundFromStrictPredecessorLe",
            "Lower bound via predecessor",
            "A numeric lower bound follows from a strict predecessor comparison",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericLowerBoundFromStrictPredecessorLe",
            "由前驱得下界",
            "由严格前驱比较得到数值下界",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "由前驅得下界",
                "嚴格前驅比較得數值下界",
            ),
            OutputLanguage::French => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "Borne inférieure via prédécesseur",
                "Une borne numérique inférieure découle d'une comparaison stricte du prédécesseur",
            ),
            OutputLanguage::Russian => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "Нижняя граница через предыдущее значение",
                "Числовая нижняя граница следует из строгого сравнения предыдущего значения",
            ),
            OutputLanguage::Spanish => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "Cota inferior por predecesor",
                "Una cota inferior numérica se deduce de comparación estricta del predecesor",
            ),
            OutputLanguage::Arabic => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "حد أدنى عبر السابق",
                "ينتج الحد الأدنى العددي من مقارنة صارمة للسابق",
            ),
            OutputLanguage::Japanese => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "直前の値による下界",
                "直前の値の狭義比較から数値下界を導きます",
            ),
            OutputLanguage::Korean => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "이전 값으로 하한",
                "이전 값의 엄격한 비교로 수치 하한을 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NumericLowerBoundFromStrictPredecessorLe",
                "Cận dưới qua giá trị liền trước",
                "Cận dưới số suy ra từ so sánh nghiêm ngặt với giá trị liền trước",
            ),
        }
    }
}

impl NumericUpperBoundWeakenLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLe",
            "Weaken numeric upper (≤)",
            "A numeric upper bound weakens under ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "NumericUpperBoundWeakenLe",
            "放宽数值上界（≤）",
            "数值上界在 ≤ 下可放宽",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "NumericUpperBoundWeakenLe",
                "放寬數值上界（≤）",
                "數值上界依 ≤ 放寬",
            ),
            OutputLanguage::French => text(
                "NumericUpperBoundWeakenLe",
                "Relâchement de borne supérieure (≤)",
                "Une borne supérieure numérique se relâche sous ≤",
            ),
            OutputLanguage::Russian => text(
                "NumericUpperBoundWeakenLe",
                "Ослабление верхней границы (≤)",
                "Числовая верхняя граница ослабляется по ≤",
            ),
            OutputLanguage::Spanish => text(
                "NumericUpperBoundWeakenLe",
                "Debilitar cota superior (≤)",
                "Una cota superior numérica se debilita bajo ≤",
            ),
            OutputLanguage::Arabic => text(
                "NumericUpperBoundWeakenLe",
                "إضعاف الحد الأعلى (≤)",
                "الحد الأعلى العددي يضعف تحت ≤",
            ),
            OutputLanguage::Japanese => text(
                "NumericUpperBoundWeakenLe",
                "数値上界の緩和（≤）",
                "数値の上界を ≤ で緩めます",
            ),
            OutputLanguage::Korean => text(
                "NumericUpperBoundWeakenLe",
                "수치 상한 완화 (≤)",
                "수치 상한을 ≤로 완화합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "NumericUpperBoundWeakenLe",
                "Nới cận trên (≤)",
                "Cận trên số được nới theo ≤",
            ),
        }
    }
}

impl IntegerSuccessorLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntegerSuccessorLe",
            "n ≤ n+1",
            "An integer is ≤ its successor",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntegerSuccessorLe", "n ≤ n+1", "整数 ≤ 其后继")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("IntegerSuccessorLe", "n ≤ n+1", "整數 ≤ 其後繼")
            }
            OutputLanguage::French => text(
                "IntegerSuccessorLe",
                "n ≤ n+1",
                "Un entier est ≤ à son successeur",
            ),
            OutputLanguage::Russian => text(
                "IntegerSuccessorLe",
                "n ≤ n+1",
                "Целое число ≤ следующего значения",
            ),
            OutputLanguage::Spanish => text(
                "IntegerSuccessorLe",
                "n ≤ n+1",
                "Un entero es ≤ a su sucesor",
            ),
            OutputLanguage::Arabic => text("IntegerSuccessorLe", "n ≤ n+1", "العدد الصحيح ≤ تاليه"),
            OutputLanguage::Japanese => {
                text("IntegerSuccessorLe", "n ≤ n+1", "整数はその後続値以下です")
            }
            OutputLanguage::Korean => text(
                "IntegerSuccessorLe",
                "n ≤ n+1",
                "정수는 그 다음 값 이하입니다",
            ),
            OutputLanguage::Vietnamese => {
                text("IntegerSuccessorLe", "n ≤ n+1", "Số nguyên ≤ số liền sau")
            }
        }
    }
}

impl IntegerAdjacencyLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntegerAdjacencyLe",
            "Integer adjacency ≤",
            "Adjacent integers compare by ≤",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntegerAdjacencyLe", "整数相邻 ≤", "相邻整数按 ≤ 比较")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("IntegerAdjacencyLe", "相鄰整數 ≤", "相鄰整數符合 ≤")
            }
            OutputLanguage::French => text(
                "IntegerAdjacencyLe",
                "Entiers adjacents ≤",
                "Les entiers adjacents se comparent par ≤",
            ),
            OutputLanguage::Russian => text(
                "IntegerAdjacencyLe",
                "Соседние целые ≤",
                "Соседние целые сравниваются по ≤",
            ),
            OutputLanguage::Spanish => text(
                "IntegerAdjacencyLe",
                "Enteros adyacentes ≤",
                "Enteros adyacentes se comparan por ≤",
            ),
            OutputLanguage::Arabic => text(
                "IntegerAdjacencyLe",
                "أعداد صحيحة متجاورة ≤",
                "الأعداد الصحيحة المتجاورة تقارن بـ ≤",
            ),
            OutputLanguage::Japanese => text(
                "IntegerAdjacencyLe",
                "隣接整数 ≤",
                "隣接する整数は ≤ で比較されます",
            ),
            OutputLanguage::Korean => text(
                "IntegerAdjacencyLe",
                "인접 정수 ≤",
                "인접한 정수는 ≤로 비교됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "IntegerAdjacencyLe",
                "Số nguyên kề nhau ≤",
                "Các số nguyên kề nhau so sánh theo ≤",
            ),
        }
    }
}

impl IntegerPredecessorLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntegerPredecessorLe",
            "n-1 ≤ n",
            "An integer predecessor is ≤ the integer",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("IntegerPredecessorLe", "n-1 ≤ n", "整数前驱 ≤ 该整数")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
                text("IntegerPredecessorLe", "n-1 ≤ n", "整數前驅 ≤ 該整數")
            }
            OutputLanguage::French => text(
                "IntegerPredecessorLe",
                "n-1 ≤ n",
                "Le prédécesseur d'un entier est ≤ à cet entier",
            ),
            OutputLanguage::Russian => text(
                "IntegerPredecessorLe",
                "n-1 ≤ n",
                "Предыдущее целое ≤ исходного целого",
            ),
            OutputLanguage::Spanish => text(
                "IntegerPredecessorLe",
                "n-1 ≤ n",
                "El predecesor de un entero es ≤ al entero",
            ),
            OutputLanguage::Arabic => text(
                "IntegerPredecessorLe",
                "n-1 ≤ n",
                "سابق العدد الصحيح ≤ ذلك العدد",
            ),
            OutputLanguage::Japanese => text(
                "IntegerPredecessorLe",
                "n-1 ≤ n",
                "直前の整数はその整数以下です",
            ),
            OutputLanguage::Korean => text(
                "IntegerPredecessorLe",
                "n-1 ≤ n",
                "정수의 이전 값은 그 정수 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "IntegerPredecessorLe",
                "n-1 ≤ n",
                "Số nguyên liền trước ≤ số nguyên đó",
            ),
        }
    }
}

impl IntegerDiffAtLeastOneLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntegerDiffAtLeastOneLe",
            "Integer gap ≥ 1",
            "Distinct integers differ by at least one",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntegerDiffAtLeastOneLe",
            "整数间隔 ≥ 1",
            "不同整数至少相差 1",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntegerDiffAtLeastOneLe",
                "整數差距 ≥ 1",
                "不同整數至少相差一",
            ),
            OutputLanguage::French => text(
                "IntegerDiffAtLeastOneLe",
                "Écart entier ≥ 1",
                "Des entiers distincts diffèrent d'au moins un",
            ),
            OutputLanguage::Russian => text(
                "IntegerDiffAtLeastOneLe",
                "Целочисленный промежуток ≥ 1",
                "Различные целые отличаются хотя бы на единицу",
            ),
            OutputLanguage::Spanish => text(
                "IntegerDiffAtLeastOneLe",
                "Brecha entera ≥ 1",
                "Enteros distintos difieren al menos en uno",
            ),
            OutputLanguage::Arabic => text(
                "IntegerDiffAtLeastOneLe",
                "فجوة صحيحة ≥ 1",
                "الأعداد الصحيحة المختلفة تختلف بواحد على الأقل",
            ),
            OutputLanguage::Japanese => text(
                "IntegerDiffAtLeastOneLe",
                "整数の差 ≥ 1",
                "異なる整数は少なくとも一だけ異なります",
            ),
            OutputLanguage::Korean => text(
                "IntegerDiffAtLeastOneLe",
                "정수 간격 ≥ 1",
                "서로 다른 정수는 적어도 1만큼 차이납니다",
            ),
            OutputLanguage::Vietnamese => text(
                "IntegerDiffAtLeastOneLe",
                "Khoảng cách nguyên ≥ 1",
                "Các số nguyên khác nhau chênh ít nhất một",
            ),
        }
    }
}

impl FiniteSetMaxMemberLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetMaxMemberLe",
            "max member ≤",
            "Every member of a finite set is ≤ its maximum",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetMaxMemberLe",
            "元素 ≤ 最大值",
            "有限集每个元素 ≤ 其最大值",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetMaxMemberLe",
                "成員 ≤ 最大值",
                "有限集合每個成員 ≤ 其最大值",
            ),
            OutputLanguage::French => text(
                "FiniteSetMaxMemberLe",
                "Membre ≤ maximum",
                "Chaque membre d'un ensemble fini est ≤ à son maximum",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetMaxMemberLe",
                "Элемент ≤ максимум",
                "Каждый элемент конечного множества ≤ его максимума",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetMaxMemberLe",
                "Miembro ≤ máximo",
                "Cada miembro de conjunto finito es ≤ a su máximo",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetMaxMemberLe",
                "عنصر ≤ القيمة العظمى",
                "كل عنصر من مجموعة منتهية ≤ قيمتها العظمى",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetMaxMemberLe",
                "要素 ≤ 最大値",
                "有限集合の各要素はその最大値以下です",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetMaxMemberLe",
                "원소 ≤ 최댓값",
                "유한 집합의 모든 원소는 최댓값 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetMaxMemberLe",
                "Phần tử ≤ lớn nhất",
                "Mọi phần tử của tập hữu hạn ≤ giá trị lớn nhất",
            ),
        }
    }
}

impl FiniteSetMinMemberLeBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetMinMemberLe",
            "min ≤ member",
            "The minimum of a finite set is ≤ every member",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetMinMemberLe",
            "最小值 ≤ 元素",
            "有限集最小值 ≤ 每个元素",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetMinMemberLe",
                "最小值 ≤ 成員",
                "有限集合的最小值 ≤ 每個成員",
            ),
            OutputLanguage::French => text(
                "FiniteSetMinMemberLe",
                "Minimum ≤ membre",
                "Le minimum d'un ensemble fini est ≤ à chaque membre",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetMinMemberLe",
                "Минимум ≤ элемент",
                "Минимум конечного множества ≤ каждого элемента",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetMinMemberLe",
                "Mínimo ≤ miembro",
                "El mínimo de conjunto finito es ≤ a cada miembro",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetMinMemberLe",
                "القيمة الصغرى ≤ عنصر",
                "القيمة الصغرى لمجموعة منتهية ≤ كل عنصر",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetMinMemberLe",
                "最小値 ≤ 要素",
                "有限集合の最小値は各要素以下です",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetMinMemberLe",
                "최솟값 ≤ 원소",
                "유한 집합의 최솟값은 모든 원소 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetMinMemberLe",
                "Nhỏ nhất ≤ phần tử",
                "Giá trị nhỏ nhất của tập hữu hạn ≤ mọi phần tử",
            ),
        }
    }
}

impl FiniteSetSizeUnionLeSumBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeUnionLeSum",
            "|A∪B| ≤ |A|+|B|",
            "Finite-set union size is at most the sum of sizes",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeUnionLeSum",
            "|A∪B| ≤ |A|+|B|",
            "有限并集大小不超过各大小之和",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "有限集合聯集大小至多為大小之和",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "La taille d'une union finie ne dépasse pas la somme des tailles",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "Размер объединения конечных множеств не больше суммы размеров",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "El tamaño de unión finita no supera la suma de tamaños",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "حجم اتحاد مجموعتين منتهيتين لا يزيد على مجموع حجميهما",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "有限集合の和の大きさは各大きさの和以下です",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "유한 집합의 합집합 크기는 각 크기의 합 이하입니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeUnionLeSum",
                "|A∪B| ≤ |A|+|B|",
                "Kích thước hợp tập hữu hạn không vượt tổng kích thước",
            ),
        }
    }
}

impl FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSurjectionCodomainLeDomain",
            "|codomain| ≤ |domain|",
            "A surjection implies the codomain is no larger than the domain",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "FiniteSetSizeSurjectionCodomainLeDomain",
            "|值域| ≤ |定义域|",
            "满射蕴含值域不大于定义域",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|陪域| ≤ |定義域|",
                "滿射推出陪域不大於定義域",
            ),
            OutputLanguage::French => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|codomaine| ≤ |domaine|",
                "Une surjection implique que le codomaine n'est pas plus grand que le domaine",
            ),
            OutputLanguage::Russian => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|область_значений| ≤ |область_определения|",
                "Сюръекция означает, что область значений не больше области определения",
            ),
            OutputLanguage::Spanish => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|codominio| ≤ |dominio|",
                "Una sobreyección implica que el codominio no es mayor que el dominio",
            ),
            OutputLanguage::Arabic => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|المجال_المقابل| ≤ |المجال|",
                "الشمول يستلزم أن المجال المقابل لا يزيد على المجال",
            ),
            OutputLanguage::Japanese => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|終域| ≤ |定義域|",
                "全射から終域は定義域より大きくないことを導きます",
            ),
            OutputLanguage::Korean => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|공역| ≤ |정의역|",
                "전사로 공역이 정의역보다 크지 않음을 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FiniteSetSizeSurjectionCodomainLeDomain",
                "|đối_miền| ≤ |miền_xác_định|",
                "Toàn ánh suy ra đối miền không lớn hơn miền xác định",
            ),
        }
    }
}

impl OrderFlipMulMinusOneToLessEqualBuiltinRuleProof {
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

impl OrderSignFromNegativeLiteralBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromNegativeLiteralBound",
            "Sign from negative bound",
            "A negative literal bound forces the stated order/sign",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "OrderSignFromNegativeLiteralBound",
            "由负上界得符号",
            "负的字面上界推出所述序/符号关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "OrderSignFromNegativeLiteralBound",
                "由負數界得符號",
                "負字面值界推出所述序或符號",
            ),
            OutputLanguage::French => text(
                "OrderSignFromNegativeLiteralBound",
                "Signe depuis une borne négative",
                "Une borne littérale négative impose l'ordre ou le signe indiqué",
            ),
            OutputLanguage::Russian => text(
                "OrderSignFromNegativeLiteralBound",
                "Знак из отрицательной границы",
                "Отрицательная литеральная граница задаёт указанный порядок или знак",
            ),
            OutputLanguage::Spanish => text(
                "OrderSignFromNegativeLiteralBound",
                "Signo desde cota negativa",
                "Una cota literal negativa fuerza el orden o signo indicado",
            ),
            OutputLanguage::Arabic => text(
                "OrderSignFromNegativeLiteralBound",
                "إشارة من حد سالب",
                "حد حرفي سالب يفرض الترتيب أو الإشارة المذكورة",
            ),
            OutputLanguage::Japanese => text(
                "OrderSignFromNegativeLiteralBound",
                "負の境界から符号",
                "負のリテラルの境界から指定された順序または符号を導きます",
            ),
            OutputLanguage::Korean => text(
                "OrderSignFromNegativeLiteralBound",
                "음수 경계로 부호",
                "음수 리터럴 경계로 명시된 순서 또는 부호를 도출합니다",
            ),
            OutputLanguage::Vietnamese => text(
                "OrderSignFromNegativeLiteralBound",
                "Dấu từ cận âm",
                "Cận literal âm suy ra thứ tự hoặc dấu đã nêu",
            ),
        }
    }
}

impl FromKnownGreaterEqualBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FromKnownGreaterEqual",
                "Known converse order",
                "The opposite-direction comparison is already known",
            ),
            OutputLanguage::ChineseTraditional => {
                text("FromKnownGreaterEqual", "已知反向序關係", "反方向比較已知")
            }
            OutputLanguage::French => text(
                "FromKnownGreaterEqual",
                "Ordre inverse connu",
                "La comparaison dans le sens opposé est déjà connue",
            ),
            OutputLanguage::Russian => text(
                "FromKnownGreaterEqual",
                "Известный обратный порядок",
                "Сравнение в обратном направлении уже известно",
            ),
            OutputLanguage::Spanish => text(
                "FromKnownGreaterEqual",
                "Orden inverso conocido",
                "La comparación en sentido opuesto ya es conocida",
            ),
            OutputLanguage::Arabic => text(
                "FromKnownGreaterEqual",
                "ترتيب عكسي معلوم",
                "المقارنة في الاتجاه المعاكس معلومة بالفعل",
            ),
            OutputLanguage::Japanese => text(
                "FromKnownGreaterEqual",
                "既知の逆向きの順序",
                "逆向きの比較は既知です",
            ),
            OutputLanguage::Korean => text(
                "FromKnownGreaterEqual",
                "알려진 역방향 순서",
                "반대 방향의 비교가 이미 알려져 있습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "FromKnownGreaterEqual",
                "Thứ tự đảo chiều đã biết",
                "So sánh theo chiều ngược đã biết",
            ),

            OutputLanguage::Chinese => text(
                "FromKnownGreaterEqual",
                "已知反向序关系",
                "引用已知的反向比较事实",
            ),
        }
    }
}

impl PositiveCommonDivisorLeGcdBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("PositiveCommonDivisorLeGcd", "Common positive divisor bound", "A positive divisor of both inputs is at most their positive gcd"),
            OutputLanguage::Chinese => text("PositiveCommonDivisorLeGcd", "公共正因子上界", "两个整数的公共正因子不超过它们的正最大公因子"),
            OutputLanguage::ChineseTraditional => text("PositiveCommonDivisorLeGcd", "公共正因數上界", "兩個整數的公共正因數不超過它們的正最大公因數"),
            OutputLanguage::French => text("PositiveCommonDivisorLeGcd", "Borne du diviseur positif commun", "Un diviseur positif des deux entiers est inférieur ou égal à leur PGCD positif"),
            OutputLanguage::Russian => text("PositiveCommonDivisorLeGcd", "Граница общего положительного делителя", "Общий положительный делитель не превосходит положительный НОД"),
            OutputLanguage::Spanish => text("PositiveCommonDivisorLeGcd", "Cota del divisor positivo común", "Un divisor positivo de ambos enteros no supera su máximo común divisor positivo"),
            OutputLanguage::Arabic => text("PositiveCommonDivisorLeGcd", "حد القاسم الموجب المشترك", "القاسم الموجب المشترك للعددين لا يتجاوز القاسم المشترك الأكبر الموجب"),
            OutputLanguage::Japanese => text("PositiveCommonDivisorLeGcd", "正の公約数の上界", "両整数の正の公約数は正の最大公約数以下です"),
            OutputLanguage::Korean => text("PositiveCommonDivisorLeGcd", "양의 공약수 상한", "두 정수의 양의 공약수는 양의 최대공약수 이하입니다"),
            OutputLanguage::Vietnamese => text("PositiveCommonDivisorLeGcd", "Cận của ước chung dương", "Ước chung dương của hai số nguyên không vượt quá ước chung lớn nhất dương"),
        }
    }
}
