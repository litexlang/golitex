//! GreaterEqual (`a >= b`) builtin explain + cite.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::{
    FromKnownLessEqualBuiltinRuleProof,

    ClosedNumericComparisonBuiltinRuleProof, FiniteSetSizeAtLeastOneBuiltinRuleProof,
    FiniteSetSizeNonnegativeBuiltinRuleProof, FromKnownGreaterBuiltinRuleProof,
    FromKnownInPositiveNaturalBuiltinRuleProof,
    GreaterEqualFactSearchProofByBuiltinRule, OrderReflexivityBuiltinRuleProof,
    PredecessorNonNegFromAtLeastOneBuiltinRuleProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_flip_mul_minus_one::OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof;
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;

use crate::json_output::explain::text::text;

impl GreaterEqualFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text("Subtract from a stored numeric bound", "The stored upper or lower bound remains sufficient after subtracting the closed constant"),
            Self::ComplexModulusNonnegative => text("Nonnegative complex modulus", "The principal complex modulus is nonnegative"),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_en(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_en(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_en(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_en(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_en(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_en(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_en(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_en(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text(
                "从已有数值界减去常数",
                "已有上界或下界减去闭式常数后满足目标弱序界",
            ),
            Self::ComplexModulusNonnegative => text(
                "复数模长非负",
                "复数模长取非负主根",
            ),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_zh(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_zh(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_zh(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_zh(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_zh(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_zh(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_zh(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_zh(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text(
                "從已有數值界減去常數",
                "已有上界或下界減去封閉常數後仍足以滿足目標",
            ),
            Self::ComplexModulusNonnegative => text(
                "複數模長非負",
                "複數模長取非負主根",
            ),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_zh_hant(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_zh_hant(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_zh_hant(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_zh_hant(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_zh_hant(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_zh_hant(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text("Soustraction d'une borne numérique stockée", "La borne supérieure ou inférieure stockée reste suffisante après soustraction de la constante fermée"),
            Self::ComplexModulusNonnegative => text("Module complexe non négatif", "Le module complexe principal est non négatif"),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_fr(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_fr(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_fr(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_fr(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_fr(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_fr(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_fr(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_fr(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text("Вычитание из сохранённой числовой границы", "Сохранённая верхняя или нижняя граница остаётся достаточной после вычитания замкнутой константы"),
            Self::ComplexModulusNonnegative => text("Неотрицательный комплексный модуль", "Главный комплексный модуль неотрицателен"),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_ru(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ru(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ru(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_ru(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ru(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ru(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ru(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_ru(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text("Resta de una cota numérica almacenada", "La cota superior o inferior almacenada sigue siendo suficiente al restar la constante cerrada"),
            Self::ComplexModulusNonnegative => text("Módulo complejo no negativo", "El módulo complejo principal es no negativo"),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_es(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_es(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_es(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_es(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_es(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_es(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_es(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_es(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text(
                "طرح من حد عددي مخزن",
                "يبقى الحد الأعلى أو الأدنى المخزن كافيًا بعد طرح الثابت المغلق",
            ),
            Self::ComplexModulusNonnegative => text(
                "مقياس مركب غير سالب",
                "المقياس المركب الرئيسي غير سالب",
            ),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_ar(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ar(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ar(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_ar(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ar(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ar(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ar(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_ar(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text(
                "保存済みの数値の境界からの減算",
                "保存済みの上界または下界は閉じた定数を引いた後も十分です",
            ),
            Self::ComplexModulusNonnegative => text(
                "複素数の絶対値の非負性",
                "複素数の主絶対値は非負です",
            ),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_ja(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ja(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ja(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_ja(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ja(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ja(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ja(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_ja(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text(
                "저장된 수치 경계에서 빼기",
                "저장된 상한 또는 하한은 닫힌 상수를 뺀 후에도 충분합니다",
            ),
            Self::ComplexModulusNonnegative => text(
                "복소수 절댓값의 비음성",
                "복소수의 주 절댓값은 음이 아닙니다",
            ),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_ko(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_ko(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_ko(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_ko(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_ko(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_ko(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_ko(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_ko(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedSubtractionBound(_) => text(
                "Trừ từ cận số đã lưu",
                "Cận trên hoặc dưới đã lưu vẫn đủ sau khi trừ hằng đóng",
            ),
            Self::ComplexModulusNonnegative => text(
                "Môđun phức không âm",
                "Môđun phức chính không âm",
            ),
            Self::FromKnownLessEqual(p) => p.rule_name_and_message_vi(),
            Self::FromKnownOrderComplement(p) => p.rule_name_and_message_vi(),
            Self::FromKnownInPositiveNatural(p) => p.rule_name_and_message_vi(),
            Self::FromKnownGreater(p) => p.rule_name_and_message_vi(),
            Self::OrderReflexivity(p) => p.rule_name_and_message_vi(),
            Self::ClosedNumericComparison(p) => p.rule_name_and_message_vi(),
            Self::OrderFlipMulMinusOne(p) => p.rule_name_and_message_vi(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSizeNonnegative(p) => p.rule_name_and_message_vi(),
            Self::FiniteSetSizeAtLeastOne(p) => p.rule_name_and_message_vi(),
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
            Self::ClosedSubtractionBound(p) => Some(p.bound.cite_fact_id),
            Self::FromKnownLessEqual(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownOrderComplement(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownInPositiveNatural(p) => p.premise_proof.cite_fact_id(),
            Self::FromKnownGreater(p) => p.premise_proof.cite_fact_id(),
            Self::OrderFlipMulMinusOne(p) => p.premise_proof.cite_fact_id(),
            Self::PredecessorNonNegFromAtLeastOne(p) => p.at_least_one_proof.cite_fact_id(),
            Self::ComplexModulusNonnegative
            | Self::OrderReflexivity(_)
            | Self::ClosedNumericComparison(_)
            | Self::FiniteSetSizeNonnegative(_)
            | Self::FiniteSetSizeAtLeastOne(_) => None,
        }
    }
}

impl FromKnownInPositiveNaturalBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "From known in positive N",
            "The goal follows from a known positive-natural membership",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "已知属于正自然数",
            "目标由已知的正自然数成员关系推出",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由已知正自然數成員",
            "目標由已知正自然數成員關係得出",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Depuis une appartenance connue aux naturels positifs",
            "L'objectif découle d'une appartenance connue aux naturels positifs",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Из известной принадлежности положительным натуральным",
            "Цель следует из известной принадлежности положительным натуральным",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desde pertenencia conocida a naturales positivos",
            "El objetivo se deduce de pertenencia conocida a naturales positivos",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "من انتماء معلوم للأعداد الطبيعية الموجبة",
            "ينتج الهدف من انتماء معلوم للأعداد الطبيعية الموجبة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の正の自然数への所属から",
            "目標は既知の正の自然数への所属から導かれます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 양의 자연수 소속에서",
            "목표는 알려진 양의 자연수 소속에서 도출됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Từ sự thuộc về số tự nhiên dương đã biết",
            "Mục tiêu suy ra từ sự thuộc về số tự nhiên dương đã biết",
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

impl FromKnownGreaterBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "From known greater",
            "The weak order follows from a known strict greater fact",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "已知严格大于",
            "弱序目标由已知的严格大于推出",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由已知大於",
            "弱序由已知嚴格大於命題得出",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Depuis une inégalité supérieure connue",
            "L'ordre large découle d'une inégalité stricte supérieure connue",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Из известного большего значения",
            "Нестрогий порядок следует из известного строгого превышения",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Desde desigualdad mayor conocida",
            "El orden débil se deduce de una desigualdad estricta mayor conocida",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "من علاقة أكبر معلومة",
            "ينتج الترتيب غير الصارم من علاقة أكبر صارمة معلومة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の大なり関係から",
            "広義順序は既知の狭義の大なり命題から導かれます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 큼 관계에서",
            "약한 순서는 알려진 엄격한 큼 명제에서 도출됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Từ quan hệ lớn hơn đã biết",
            "Thứ tự không nghiêm ngặt suy ra từ quan hệ lớn hơn nghiêm ngặt đã biết",
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

impl OrderReflexivityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Order reflexivity",
            "A quantity is less-or-equal to itself",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "序的自反性",
            "任何量都不大于也不小于自己（≤ 自身）",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("序關係自反性", "任一量小於或等於自身")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Réflexivité de l'ordre",
            "Une quantité est inférieure ou égale à elle-même",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Рефлексивность порядка",
            "Величина меньше или равна самой себе",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Reflexividad del orden",
            "Una cantidad es menor o igual a sí misma",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انعكاسية الترتيب",
            "الكمية أصغر من نفسها أو تساويها",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("順序の反射性", "量は自身以下です")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "순서 반사성",
            "양은 자기 자신보다 작거나 같습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính phản xạ của thứ tự",
            "Một đại lượng nhỏ hơn hoặc bằng chính nó",
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

impl ClosedNumericComparisonBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Closed numeric comparison",
            "Both sides are closed numbers and compare as stated",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "封闭数值比较",
            "两边都是可计算的数，并满足所述比较",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "封閉數值比較",
            "兩邊為封閉數值且符合所述比較",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Comparaison numérique fermée",
            "Les deux membres sont des nombres fermés et satisfont la comparaison indiquée",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Сравнение замкнутых числовых выражений",
            "Обе части являются замкнутыми числами и удовлетворяют указанному сравнению",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Comparación numérica cerrada",
            "Ambos lados son números cerrados y cumplen la comparación indicada",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مقارنة عددية مغلقة",
            "الطرفان عددان مغلقان ويحققان المقارنة المذكورة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "閉じた数値式の比較",
            "両辺は閉じた数値であり、指定された比較を満たします",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "닫힌 수치 식 비교",
            "양변은 닫힌 수이며 명시된 비교를 만족합니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "So sánh số đóng",
            "Hai vế là số đóng và thỏa so sánh đã nêu",
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

impl PredecessorNonNegFromAtLeastOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "n-1 ≥ 0 from n ≥ 1",
            "Predecessor is nonnegative when the value is at least one",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由 n ≥ 1 得 n-1 ≥ 0",
            "当值至少为 1 时前驱非负",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由 n ≥ 1 得 n-1 ≥ 0",
            "值至少為一時，前驅非負",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "n-1 ≥ 0 depuis n ≥ 1",
            "Le prédécesseur est non négatif quand la valeur est au moins un",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "n-1 ≥ 0 из n ≥ 1",
            "Предыдущее значение неотрицательно, если исходное не меньше одного",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "n-1 ≥ 0 a partir de n ≥ 1",
            "El predecesor es no negativo si el valor es al menos uno",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "n-1 ≥ 0 من n ≥ 1",
            "السابق غير سالب عندما تكون القيمة واحدًا على الأقل",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "n ≥ 1 から n-1 ≥ 0",
            "値が少なくとも一なら直前の値は非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "n ≥ 1에서 n-1 ≥ 0",
            "값이 적어도 1이면 이전 값은 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "n-1 ≥ 0 từ n ≥ 1",
            "Giá trị liền trước không âm khi giá trị ít nhất một",
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

impl FiniteSetSizeNonnegativeBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonnegative cardinality of a finite set",
            "Finite-set size is nonnegative",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("有限集合的基数非负", "有限集大小非负")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("有限集合的基數非負", "有限集合的大小非負")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Cardinal positif ou nul d’un ensemble fini",
            "La taille d'un ensemble fini est non négative",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Неотрицательность мощности конечного множества",
            "Размер конечного множества неотрицателен",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Cardinalidad no negativa de un conjunto finito",
            "El tamaño de un conjunto finito es no negativo",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عدد عناصر المجموعة المنتهية غير سالب",
            "حجم المجموعة المنتهية غير سالب",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "有限集合の要素数の非負性",
            "有限集合の大きさは非負です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "유한집합 원소 수의 비음수성",
            "유한 집합의 크기는 음이 아닙니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Lực lượng của tập hữu hạn không âm",
            "Kích thước tập hữu hạn không âm",
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

impl FiniteSetSizeAtLeastOneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Nonempty finite set has at least one element",
            "A nonempty finite set has size at least one",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非空有限集合至少有一个元素",
            "非空有限集大小至少为 1",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "非空有限集合至少有一個元素",
            "非空有限集合的大小至少為一",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ensemble fini non vide ayant au moins un élément",
            "Un ensemble fini non vide a au moins un élément",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Непустое конечное множество содержит хотя бы один элемент",
            "Непустое конечное множество имеет размер не меньше одного",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conjunto finito no vacío con al menos un elemento",
            "Un conjunto finito no vacío tiene tamaño al menos uno",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "المجموعة المنتهية غير الخالية لها عنصر واحد على الأقل",
            "المجموعة المنتهية غير الخالية لها عنصر واحد على الأقل",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "非空の有限集合には少なくとも一つの要素がある",
            "空でない有限集合の大きさは少なくとも一です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "비어 있지 않은 유한집합에는 적어도 한 원소가 있음",
            "비어 있지 않은 유한 집합의 크기는 적어도 1입니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập hữu hạn khác rỗng có ít nhất một phần tử",
            "Tập hữu hạn không rỗng có kích thước ít nhất một",
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

impl OrderFlipMulMinusOneToGreaterEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Order flip by ×(-1)",
            "Multiplying by -1 reverses the inequality",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "乘以 -1 反转不等式",
            "两边同乘 -1 后不等式方向相反",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "乘以 -1 反轉序",
            "乘以 -1 反轉不等式方向",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inversion d'ordre par ×(-1)",
            "Multiplier par -1 inverse l'inégalité",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Обращение порядка при ×(-1)",
            "Умножение на -1 обращает неравенство",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inversión de orden por ×(-1)",
            "Multiplicar por -1 invierte la desigualdad",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "عكس الترتيب بالضرب في (-1)",
            "الضرب في -1 يعكس المتباينة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "×(-1) による順序反転",
            "-1 を掛けると不等号が反転します",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "×(-1)에 의한 순서 반전",
            "-1을 곱하면 부등호가 반전됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đảo thứ tự bởi ×(-1)",
            "Nhân với -1 đảo chiều bất đẳng thức",
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

impl FromKnownLessEqualBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Known converse order",
            "The opposite-direction comparison is already known",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "已知反向序关系",
            "引用已知的反向比较事实",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("已知反向序關係", "反方向比較已知")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ordre inverse connu",
            "La comparaison dans le sens opposé est déjà connue",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Известный обратный порядок",
            "Сравнение в обратном направлении уже известно",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Orden inverso conocido",
            "La comparación en sentido opuesto ya es conocida",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "ترتيب عكسي معلوم",
            "المقارنة في الاتجاه المعاكس معلومة بالفعل",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "既知の逆向きの順序",
            "逆向きの比較は既知です",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "알려진 역방향 순서",
            "반대 방향의 비교가 이미 알려져 있습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Thứ tự đảo chiều đã biết",
            "So sánh theo chiều ngược đã biết",
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
