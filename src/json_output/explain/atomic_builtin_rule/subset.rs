//! Leaf explain for atomic family group `subset`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::{
    IntegerRangeSubsetNumericCarrierBuiltinRuleProof,
    IntersectSubsetFromLeftUpperBoundBuiltinRuleProof,
    IntersectSubsetFromRightUpperBoundBuiltinRuleProof,
    IntersectSubsetLeftBuiltinRuleProof,
    IntersectSubsetRightBuiltinRuleProof,
    ListSetSubsetFromMembersBuiltinRuleProof,
    RealIntervalSubsetRealBuiltinRuleProof,
    SetBuilderSubsetOfParamSetBuiltinRuleProof,
    SetMinusSubsetLeftBuiltinRuleProof,
    StandardSetSubsetBuiltinRuleProof,
    SubsetCartComponentwiseBuiltinRuleProof,
    SubsetFactSearchProofByBuiltinRule,
    SubsetPowerSetMonotoneBuiltinRuleProof,
    SubsetReflexivityBuiltinRuleProof,
    SubsetSetMinusCommonRightMonotoneBuiltinRuleProof,
    SubsetTransitivityBuiltinRuleProof,
    SubsetUnionLeftBuiltinRuleProof,
    SubsetUnionRightBuiltinRuleProof,
    UnionSubsetFromBothOperandsBuiltinRuleProof,
    UnionSubsetFromComponentwiseBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl SubsetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_id_and_message(lang),
            Self::IntersectSubsetLeft(p) => p.rule_id_and_message(lang),
            Self::IntersectSubsetRight(p) => p.rule_id_and_message(lang),
            Self::SubsetUnionLeft(p) => p.rule_id_and_message(lang),
            Self::SubsetUnionRight(p) => p.rule_id_and_message(lang),
            Self::SetMinusSubsetLeft(p) => p.rule_id_and_message(lang),
            Self::RealIntervalSubsetReal(p) => p.rule_id_and_message(lang),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_id_and_message(lang),
            Self::SubsetReflexivity(p) => p.rule_id_and_message(lang),
            Self::UnionSubsetFromBothOperands(p) => p.rule_id_and_message(lang),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_id_and_message(lang),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_id_and_message(lang),
            Self::ListSetSubsetFromMembers(p) => p.rule_id_and_message(lang),
            Self::UnionSubsetFromComponentwise(p) => p.rule_id_and_message(lang),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_id_and_message(lang),
            Self::SubsetPowerSetMonotone(p) => p.rule_id_and_message(lang),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_id_and_message(lang),
            Self::SubsetCartComponentwise(p) => p.rule_id_and_message(lang),
            Self::SubsetTransitivity(p) => p.rule_id_and_message(lang),
        }
    }

    pub fn cite_fact_id(&self) -> Option<FactId> {
        match self {
            Self::StandardSetSubset(_) => None,
            Self::IntersectSubsetLeft(_) => None,
            Self::IntersectSubsetRight(_) => None,
            Self::SubsetUnionLeft(_) => None,
            Self::SubsetUnionRight(_) => None,
            Self::SetMinusSubsetLeft(_) => None,
            Self::RealIntervalSubsetReal(_) => None,
            Self::SetBuilderSubsetOfParamSet(_) => None,
            Self::SubsetReflexivity(_) => None,
            Self::UnionSubsetFromBothOperands(_) => None,
            Self::IntersectSubsetFromLeftUpperBound(_) => None,
            Self::IntersectSubsetFromRightUpperBound(_) => None,
            Self::ListSetSubsetFromMembers(_) => None,
            Self::UnionSubsetFromComponentwise(_) => None,
            Self::IntegerRangeSubsetNumericCarrier(_) => None,
            Self::SubsetPowerSetMonotone(_) => None,
            Self::SubsetSetMinusCommonRightMonotone(_) => None,
            Self::SubsetCartComponentwise(_) => None,
            Self::SubsetTransitivity(_) => None,
        }
    }
}

impl StandardSetSubsetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardSetSubset",
            "Standard Set Subset",
            "Fixed inclusion among standard number sets",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("StandardSetSubset", "标准集子集", "标准数集之间的固定包含")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "StandardSetSubset",
                "標準集合子集關係",
                "標準數集間的固定包含關係",
            ),
            OutputLanguage::French => text(
                "StandardSetSubset",
                "Inclusion d'ensembles standards",
                "Inclusion fixe entre ensembles numériques standards",
            ),
            OutputLanguage::Russian => text(
                "StandardSetSubset",
                "Включение стандартных множеств",
                "Фиксированное включение стандартных числовых множеств",
            ),
            OutputLanguage::Spanish => text(
                "StandardSetSubset",
                "Inclusión de conjuntos estándar",
                "Inclusión fija entre conjuntos numéricos estándar",
            ),
            OutputLanguage::Arabic => text(
                "StandardSetSubset",
                "احتواء مجموعات قياسية",
                "احتواء ثابت بين مجموعات الأعداد القياسية",
            ),
            OutputLanguage::Japanese => text(
                "StandardSetSubset",
                "標準集合の包含関係",
                "標準的な数集合間の固定の包含関係",
            ),
            OutputLanguage::Korean => text(
                "StandardSetSubset",
                "표준 집합 포함 관계",
                "표준 수 집합 사이의 고정된 포함 관계",
            ),
            OutputLanguage::Vietnamese => text(
                "StandardSetSubset",
                "Quan hệ tập con chuẩn",
                "Bao hàm cố định giữa các tập số chuẩn",
            ),
        }
    }
}

impl IntersectSubsetLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetLeft",
            "Intersect Subset Left",
            "`intersect(A, B) $subset A`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetLeft",
            "交是左因子的子集",
            "交是左因子的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectSubsetLeft",
                "交集為左集合子集",
                "`intersect(A, B) $subset A`",
            ),
            OutputLanguage::French => text(
                "IntersectSubsetLeft",
                "Intersection incluse à gauche",
                "`intersect(A, B) $subset A`",
            ),
            OutputLanguage::Russian => text(
                "IntersectSubsetLeft",
                "Пересечение включено в левое множество",
                "`intersect(A, B) $subset A`",
            ),
            OutputLanguage::Spanish => text(
                "IntersectSubsetLeft",
                "Intersección incluida a la izquierda",
                "`intersect(A, B) $subset A`",
            ),
            OutputLanguage::Arabic => text(
                "IntersectSubsetLeft",
                "التقاطع جزئي من اليسار",
                "`intersect(A, B) $subset A`",
            ),
            OutputLanguage::Japanese => text(
                "IntersectSubsetLeft",
                "交差の左側への包含",
                "`intersect(A, B) $subset A`",
            ),
            OutputLanguage::Korean => text(
                "IntersectSubsetLeft",
                "교집합의 왼쪽 포함",
                "`intersect(A, B) $subset A`",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectSubsetLeft",
                "Giao là tập con bên trái",
                "`intersect(A, B) $subset A`",
            ),
        }
    }
}

impl IntersectSubsetRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetRight",
            "Intersect Subset Right",
            "`intersect(A, B) $subset B`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetRight",
            "交是右因子的子集",
            "交是右因子的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectSubsetRight",
                "交集為右集合子集",
                "`intersect(A, B) $subset B`",
            ),
            OutputLanguage::French => text(
                "IntersectSubsetRight",
                "Intersection incluse à droite",
                "`intersect(A, B) $subset B`",
            ),
            OutputLanguage::Russian => text(
                "IntersectSubsetRight",
                "Пересечение включено в правое множество",
                "`intersect(A, B) $subset B`",
            ),
            OutputLanguage::Spanish => text(
                "IntersectSubsetRight",
                "Intersección incluida a la derecha",
                "`intersect(A, B) $subset B`",
            ),
            OutputLanguage::Arabic => text(
                "IntersectSubsetRight",
                "التقاطع جزئي من اليمين",
                "`intersect(A, B) $subset B`",
            ),
            OutputLanguage::Japanese => text(
                "IntersectSubsetRight",
                "交差の右側への包含",
                "`intersect(A, B) $subset B`",
            ),
            OutputLanguage::Korean => text(
                "IntersectSubsetRight",
                "교집합의 오른쪽 포함",
                "`intersect(A, B) $subset B`",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectSubsetRight",
                "Giao là tập con bên phải",
                "`intersect(A, B) $subset B`",
            ),
        }
    }
}

impl SubsetUnionLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubsetUnionLeft",
            "Subset Union Left",
            "`A $subset union(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubsetUnionLeft", "左因子是并的子集", "左因子是并的子集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SubsetUnionLeft",
                "左集合為聯集子集",
                "`A $subset union(A, B)`",
            ),
            OutputLanguage::French => text(
                "SubsetUnionLeft",
                "Opérande gauche inclus dans l'union",
                "`A $subset union(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "SubsetUnionLeft",
                "Левое множество включено в объединение",
                "`A $subset union(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "SubsetUnionLeft",
                "Operando izquierdo incluido en unión",
                "`A $subset union(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "SubsetUnionLeft",
                "اليسار جزئي من الاتحاد",
                "`A $subset union(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "SubsetUnionLeft",
                "左集合の和集合への包含",
                "`A $subset union(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "SubsetUnionLeft",
                "왼쪽 집합의 합집합 포함",
                "`A $subset union(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "SubsetUnionLeft",
                "Tập trái là tập con của hợp",
                "`A $subset union(A, B)`",
            ),
        }
    }
}

impl SubsetUnionRightBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubsetUnionRight",
            "Subset Union Right",
            "`B $subset union(A, B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubsetUnionRight", "右因子是并的子集", "右因子是并的子集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SubsetUnionRight",
                "右集合為聯集子集",
                "`B $subset union(A, B)`",
            ),
            OutputLanguage::French => text(
                "SubsetUnionRight",
                "Opérande droit inclus dans l'union",
                "`B $subset union(A, B)`",
            ),
            OutputLanguage::Russian => text(
                "SubsetUnionRight",
                "Правое множество включено в объединение",
                "`B $subset union(A, B)`",
            ),
            OutputLanguage::Spanish => text(
                "SubsetUnionRight",
                "Operando derecho incluido en unión",
                "`B $subset union(A, B)`",
            ),
            OutputLanguage::Arabic => text(
                "SubsetUnionRight",
                "اليمين جزئي من الاتحاد",
                "`B $subset union(A, B)`",
            ),
            OutputLanguage::Japanese => text(
                "SubsetUnionRight",
                "右集合の和集合への包含",
                "`B $subset union(A, B)`",
            ),
            OutputLanguage::Korean => text(
                "SubsetUnionRight",
                "오른쪽 집합의 합집합 포함",
                "`B $subset union(A, B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "SubsetUnionRight",
                "Tập phải là tập con của hợp",
                "`B $subset union(A, B)`",
            ),
        }
    }
}

impl SetMinusSubsetLeftBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetMinusSubsetLeft",
            "Set Minus Subset Left",
            "`set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetMinusSubsetLeft",
            "差集是左因子的子集",
            "差集是左因子的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetMinusSubsetLeft",
                "差集為左集合子集",
                "`set_minus(A, B) $subset A`",
            ),
            OutputLanguage::French => text(
                "SetMinusSubsetLeft",
                "Différence incluse à gauche",
                "`set_minus(A, B) $subset A`",
            ),
            OutputLanguage::Russian => text(
                "SetMinusSubsetLeft",
                "Разность включена в левое множество",
                "`set_minus(A, B) $subset A`",
            ),
            OutputLanguage::Spanish => text(
                "SetMinusSubsetLeft",
                "Diferencia incluida a la izquierda",
                "`set_minus(A, B) $subset A`",
            ),
            OutputLanguage::Arabic => text(
                "SetMinusSubsetLeft",
                "الفرق جزئي من اليسار",
                "`set_minus(A, B) $subset A`",
            ),
            OutputLanguage::Japanese => text(
                "SetMinusSubsetLeft",
                "差集合の左側への包含",
                "`set_minus(A, B) $subset A`",
            ),
            OutputLanguage::Korean => text(
                "SetMinusSubsetLeft",
                "차집합의 왼쪽 포함",
                "`set_minus(A, B) $subset A`",
            ),
            OutputLanguage::Vietnamese => text(
                "SetMinusSubsetLeft",
                "Hiệu là tập con bên trái",
                "`set_minus(A, B) $subset A`",
            ),
        }
    }
}

impl RealIntervalSubsetRealBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "RealIntervalSubsetReal",
            "Real Interval Subset Real",
            "Real intervals inhabit R",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "RealIntervalSubsetReal",
            "实区间是 R 的子集",
            "实区间是实数集的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "RealIntervalSubsetReal",
                "實數區間為實數集子集",
                "實數區間包含於 R",
            ),
            OutputLanguage::French => text(
                "RealIntervalSubsetReal",
                "Intervalle réel inclus dans les réels",
                "Les intervalles réels sont inclus dans R",
            ),
            OutputLanguage::Russian => text(
                "RealIntervalSubsetReal",
                "Вещественный интервал включён в вещественные",
                "Вещественные интервалы содержатся в R",
            ),
            OutputLanguage::Spanish => text(
                "RealIntervalSubsetReal",
                "Intervalo real incluido en los reales",
                "Los intervalos reales están incluidos en R",
            ),
            OutputLanguage::Arabic => text(
                "RealIntervalSubsetReal",
                "فترة حقيقية جزئية من الأعداد الحقيقية",
                "الفترات الحقيقية محتواة في R",
            ),
            OutputLanguage::Japanese => text(
                "RealIntervalSubsetReal",
                "実数区間の実数集合への包含",
                "実数区間は R に含まれます",
            ),
            OutputLanguage::Korean => text(
                "RealIntervalSubsetReal",
                "실수 구간의 실수 집합 포함",
                "실수 구간은 R에 포함됩니다",
            ),
            OutputLanguage::Vietnamese => text(
                "RealIntervalSubsetReal",
                "Khoảng thực là tập con số thực",
                "Các khoảng thực nằm trong R",
            ),
        }
    }
}

impl SetBuilderSubsetOfParamSetBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SetBuilderSubsetOfParamSet",
            "Set Builder Subset Of Param Set",
            "`{x S: P…} $subset S`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SetBuilderSubsetOfParamSet",
            "集合构造子集于参数集",
            "集合构造式是参数集的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SetBuilderSubsetOfParamSet",
                "集合構造為參數集合子集",
                "`{x S: P…} $subset S`",
            ),
            OutputLanguage::French => text(
                "SetBuilderSubsetOfParamSet",
                "Ensemble défini en compréhension inclus dans son ensemble paramètre",
                "`{x S: P…} $subset S`",
            ),
            OutputLanguage::Russian => text(
                "SetBuilderSubsetOfParamSet",
                "Множество по условию включено в параметрическое множество",
                "`{x S: P…} $subset S`",
            ),
            OutputLanguage::Spanish => text(
                "SetBuilderSubsetOfParamSet",
                "Conjunto por comprensión incluido en conjunto parámetro",
                "`{x S: P…} $subset S`",
            ),
            OutputLanguage::Arabic => text(
                "SetBuilderSubsetOfParamSet",
                "المجموعة المبنية جزئية من مجموعة المعامل",
                "`{x S: P…} $subset S`",
            ),
            OutputLanguage::Japanese => text(
                "SetBuilderSubsetOfParamSet",
                "内包表記集合のパラメータ集合への包含",
                "`{x S: P…} $subset S`",
            ),
            OutputLanguage::Korean => text(
                "SetBuilderSubsetOfParamSet",
                "조건제시 집합의 매개변수 집합 포함",
                "`{x S: P…} $subset S`",
            ),
            OutputLanguage::Vietnamese => text(
                "SetBuilderSubsetOfParamSet",
                "Tập dựng là tập con của tập tham số",
                "`{x S: P…} $subset S`",
            ),
        }
    }
}

impl SubsetReflexivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubsetReflexivity",
            "Subset Reflexivity",
            "Reflexivity: `A $subset A`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubsetReflexivity", "子集自反", "任意集合是自身的子集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SubsetReflexivity",
                "子集關係自反性",
                "自反性：`A $subset A`",
            ),
            OutputLanguage::French => text(
                "SubsetReflexivity",
                "Réflexivité de l'inclusion",
                "Réflexivité : `A $subset A`",
            ),
            OutputLanguage::Russian => text(
                "SubsetReflexivity",
                "Рефлексивность включения",
                "Рефлексивность: `A $subset A`",
            ),
            OutputLanguage::Spanish => text(
                "SubsetReflexivity",
                "Reflexividad de inclusión",
                "Reflexividad: `A $subset A`",
            ),
            OutputLanguage::Arabic => text(
                "SubsetReflexivity",
                "انعكاسية الاحتواء الجزئي",
                "الانعكاسية: `A $subset A`",
            ),
            OutputLanguage::Japanese => {
                text("SubsetReflexivity", "包含の反射性", "反射性：`A $subset A`")
            }
            OutputLanguage::Korean => text(
                "SubsetReflexivity",
                "부분집합 반사성",
                "반사성: `A $subset A`",
            ),
            OutputLanguage::Vietnamese => text(
                "SubsetReflexivity",
                "Tính phản xạ của tập con",
                "Tính phản xạ: `A $subset A`",
            ),
        }
    }
}

impl UnionSubsetFromBothOperandsBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionSubsetFromBothOperands",
            "Union Subset From Both Operands",
            "`A $subset S` and `B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionSubsetFromBothOperands",
            "两边子集推出并是子集",
            "两边都是子集则其并也是子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionSubsetFromBothOperands",
                "由兩運算元得聯集子集",
                "`A $subset S` 與 `B $subset S` ⇒ `union(A, B) $subset S`",
            ),
            OutputLanguage::French => text(
                "UnionSubsetFromBothOperands",
                "Inclusion de l'union depuis les deux opérandes",
                "`A $subset S` et `B $subset S` ⇒ `union(A, B) $subset S`",
            ),
            OutputLanguage::Russian => text(
                "UnionSubsetFromBothOperands",
                "Включение объединения по обоим операндам",
                "`A $subset S` и `B $subset S` ⇒ `union(A, B) $subset S`",
            ),
            OutputLanguage::Spanish => text(
                "UnionSubsetFromBothOperands",
                "Inclusión de unión desde ambos operandos",
                "`A $subset S` y `B $subset S` ⇒ `union(A, B) $subset S`",
            ),
            OutputLanguage::Arabic => text(
                "UnionSubsetFromBothOperands",
                "احتواء الاتحاد من المعاملين",
                "`A $subset S` و`B $subset S` ⇒ `union(A, B) $subset S`",
            ),
            OutputLanguage::Japanese => text(
                "UnionSubsetFromBothOperands",
                "両被演算子から和集合の包含",
                "`A $subset S` かつ `B $subset S` ⇒ `union(A, B) $subset S`",
            ),
            OutputLanguage::Korean => text(
                "UnionSubsetFromBothOperands",
                "두 피연산자로 합집합 포함",
                "`A $subset S` 및 `B $subset S` ⇒ `union(A, B) $subset S`",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionSubsetFromBothOperands",
                "Bao hàm hợp từ hai toán hạng",
                "`A $subset S` và `B $subset S` ⇒ `union(A, B) $subset S`",
            ),
        }
    }
}

impl IntersectSubsetFromLeftUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetFromLeftUpperBound",
            "Intersect Subset From Left Upper Bound",
            "`A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetFromLeftUpperBound",
            "左上界推出交是子集",
            "左因子是子集则交也是子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectSubsetFromLeftUpperBound",
                "交集繼承左集合上界",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::French => text(
                "IntersectSubsetFromLeftUpperBound",
                "Borne d'inclusion de l'intersection depuis la gauche",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Russian => text(
                "IntersectSubsetFromLeftUpperBound",
                "Включение пересечения по левой верхней границе",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Spanish => text(
                "IntersectSubsetFromLeftUpperBound",
                "Inclusión de intersección por cota izquierda",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Arabic => text(
                "IntersectSubsetFromLeftUpperBound",
                "احتواء التقاطع من الحد الأعلى الأيسر",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Japanese => text(
                "IntersectSubsetFromLeftUpperBound",
                "左側の上界から交差の包含",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Korean => text(
                "IntersectSubsetFromLeftUpperBound",
                "왼쪽 상한으로 교집합 포함",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectSubsetFromLeftUpperBound",
                "Bao hàm giao từ cận trên trái",
                "`A $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
        }
    }
}

impl IntersectSubsetFromRightUpperBoundBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetFromRightUpperBound",
            "Intersect Subset From Right Upper Bound",
            "`B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntersectSubsetFromRightUpperBound",
            "右上界推出交是子集",
            "右因子是子集则交也是子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "IntersectSubsetFromRightUpperBound",
                "交集繼承右集合上界",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::French => text(
                "IntersectSubsetFromRightUpperBound",
                "Borne d'inclusion de l'intersection depuis la droite",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Russian => text(
                "IntersectSubsetFromRightUpperBound",
                "Включение пересечения по правой верхней границе",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Spanish => text(
                "IntersectSubsetFromRightUpperBound",
                "Inclusión de intersección por cota derecha",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Arabic => text(
                "IntersectSubsetFromRightUpperBound",
                "احتواء التقاطع من الحد الأعلى الأيمن",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Japanese => text(
                "IntersectSubsetFromRightUpperBound",
                "右側の上界から交差の包含",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Korean => text(
                "IntersectSubsetFromRightUpperBound",
                "오른쪽 상한으로 교집합 포함",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
            OutputLanguage::Vietnamese => text(
                "IntersectSubsetFromRightUpperBound",
                "Bao hàm giao từ cận trên phải",
                "`B $subset S` ⇒ `intersect(A, B) $subset S`",
            ),
        }
    }
}

impl ListSetSubsetFromMembersBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "ListSetSubsetFromMembers",
            "List Set Subset From Members",
            "`{a1, …, an} $subset S` from each `ai $in S`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "ListSetSubsetFromMembers",
            "列表元素推出列表集是子集",
            "各元素属于则列表集是子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "ListSetSubsetFromMembers",
                "由成員關係得列表集合子集",
                "每個 `ai $in S` 推出 `{a1, …, an} $subset S`",
            ),
            OutputLanguage::French => text(
                "ListSetSubsetFromMembers",
                "Inclusion d'ensemble liste par ses membres",
                "`{a1, …, an} $subset S` depuis chaque `ai $in S`",
            ),
            OutputLanguage::Russian => text(
                "ListSetSubsetFromMembers",
                "Включение списочного множества по элементам",
                "`{a1, …, an} $subset S` из каждого `ai $in S`",
            ),
            OutputLanguage::Spanish => text(
                "ListSetSubsetFromMembers",
                "Inclusión de conjunto de lista por miembros",
                "`{a1, …, an} $subset S` a partir de cada `ai $in S`",
            ),
            OutputLanguage::Arabic => text(
                "ListSetSubsetFromMembers",
                "احتواء مجموعة قائمة من عناصرها",
                "`{a1, …, an} $subset S` من كل `ai $in S`",
            ),
            OutputLanguage::Japanese => text(
                "ListSetSubsetFromMembers",
                "要素の所属からリスト集合の包含",
                "各 `ai $in S` から `{a1, …, an} $subset S`",
            ),
            OutputLanguage::Korean => text(
                "ListSetSubsetFromMembers",
                "원소 소속으로 목록 집합 포함",
                "각 `ai $in S`에서 `{a1, …, an} $subset S`",
            ),
            OutputLanguage::Vietnamese => text(
                "ListSetSubsetFromMembers",
                "Tập danh sách là tập con từ phần tử",
                "`{a1, …, an} $subset S` từ mỗi `ai $in S`",
            ),
        }
    }
}

impl UnionSubsetFromComponentwiseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "UnionSubsetFromComponentwise",
            "Union Subset From Componentwise",
            "`union(A, B) $subset union(C, D)` from componentwise subsets",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "UnionSubsetFromComponentwise",
            "分量子集推出并是子集",
            "分量子集推出并集子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "UnionSubsetFromComponentwise",
                "由逐分量關係得聯集子集",
                "逐分量子集關係推出 `union(A, B) $subset union(C, D)`",
            ),
            OutputLanguage::French => text(
                "UnionSubsetFromComponentwise",
                "Inclusion de l'union par composantes",
                "`union(A, B) $subset union(C, D)` par les inclusions composante par composante",
            ),
            OutputLanguage::Russian => text(
                "UnionSubsetFromComponentwise",
                "Включение объединения покомпонентно",
                "`union(A, B) $subset union(C, D)` из покомпонентных включений",
            ),
            OutputLanguage::Spanish => text(
                "UnionSubsetFromComponentwise",
                "Inclusión de unión por componentes",
                "`union(A, B) $subset union(C, D)` por inclusiones componente a componente",
            ),
            OutputLanguage::Arabic => text(
                "UnionSubsetFromComponentwise",
                "احتواء الاتحاد بالمكونات",
                "`union(A, B) $subset union(C, D)` من الاحتواء بالمكونات",
            ),
            OutputLanguage::Japanese => text(
                "UnionSubsetFromComponentwise",
                "成分ごとの関係から和集合の包含",
                "成分ごとの包含から `union(A, B) $subset union(C, D)`",
            ),
            OutputLanguage::Korean => text(
                "UnionSubsetFromComponentwise",
                "성분별 관계로 합집합 포함",
                "성분별 부분집합에서 `union(A, B) $subset union(C, D)`",
            ),
            OutputLanguage::Vietnamese => text(
                "UnionSubsetFromComponentwise",
                "Bao hàm hợp theo thành phần",
                "`union(A, B) $subset union(C, D)` từ quan hệ tập con từng thành phần",
            ),
        }
    }
}

impl IntegerRangeSubsetNumericCarrierBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "Integer Range Subset Numeric Carrier",
            "Integer `range` / `closed_range` sits in its numeric carrier",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "整数区间属于数值载体",
            "整数区间落在其数值载体中",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "整數區間為數值載體的子集",
            "整數 `range` 或 `closed_range` 包含於其數值載體",
        )
    },
            OutputLanguage::French => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "Intervalle entier inclus dans son ensemble numérique porteur",
            "Un `range` ou `closed_range` entier est inclus dans son ensemble numérique porteur",
        )
    },
            OutputLanguage::Russian => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "Целочисленный интервал является подмножеством числового носителя",
            "Целочисленный `range` или `closed_range` содержится в числовом носителе",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "Intervalo entero subconjunto de portador numérico",
            "El `range` o `closed_range` entero está incluido en su portador numérico",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "فترة صحيحة جزئية من المجموعة الحاملة العددية",
            "`range` أو `closed_range` الصحيح محتوى في مجموعته الحاملة العددية",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "整数区間の数値台集合への包含",
            "整数の `range` または `closed_range` は数値台集合に含まれます",
        )
    },
            OutputLanguage::Korean => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "정수 구간의 수치 바탕 집합 포함",
            "정수 `range` 또는 `closed_range`는 수치 바탕 집합에 포함됩니다",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "IntegerRangeSubsetNumericCarrier",
            "Khoảng nguyên là tập con của tập nền số",
            "`range` hoặc `closed_range` nguyên nằm trong tập nền số của nó",
        )
    },

        }
    }
}

impl SubsetPowerSetMonotoneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubsetPowerSetMonotone",
            "Subset Power Set Monotone",
            "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SubsetPowerSetMonotone",
            "幂集对子集单调",
            "子集关系在幂集上单调",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SubsetPowerSetMonotone",
                "冪集子集單調性",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
            OutputLanguage::French => text(
                "SubsetPowerSetMonotone",
                "Monotonie d'inclusion de l'ensemble des parties",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
            OutputLanguage::Russian => text(
                "SubsetPowerSetMonotone",
                "Монотонность включения множества подмножеств",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
            OutputLanguage::Spanish => text(
                "SubsetPowerSetMonotone",
                "Monotonía de inclusión del conjunto potencia",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
            OutputLanguage::Arabic => text(
                "SubsetPowerSetMonotone",
                "رتابة احتواء مجموعة القوى",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
            OutputLanguage::Japanese => text(
                "SubsetPowerSetMonotone",
                "べき集合の包含の単調性",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
            OutputLanguage::Korean => text(
                "SubsetPowerSetMonotone",
                "멱집합 포함 단조성",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
            OutputLanguage::Vietnamese => text(
                "SubsetPowerSetMonotone",
                "Đơn điệu tập con của tập lũy thừa",
                "`A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
            ),
        }
    }
}

impl SubsetSetMinusCommonRightMonotoneBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubsetSetMinusCommonRightMonotone",
            "Subset Set Minus Common Right Monotone",
            "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SubsetSetMinusCommonRightMonotone",
            "同右差集对子集单调",
            "同右差集保持子集关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SubsetSetMinusCommonRightMonotone",
                "差集共用右集合的子集單調性",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
            OutputLanguage::French => text(
                "SubsetSetMinusCommonRightMonotone",
                "Monotonie de différence à opérande droit commun",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
            OutputLanguage::Russian => text(
                "SubsetSetMinusCommonRightMonotone",
                "Монотонность разности с общим правым множеством",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
            OutputLanguage::Spanish => text(
                "SubsetSetMinusCommonRightMonotone",
                "Monotonía de diferencia con operando derecho común",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
            OutputLanguage::Arabic => text(
                "SubsetSetMinusCommonRightMonotone",
                "رتابة الفرق بمجموعة يمنى مشتركة",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
            OutputLanguage::Japanese => text(
                "SubsetSetMinusCommonRightMonotone",
                "共通の右集合を持つ差集合の単調性",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
            OutputLanguage::Korean => text(
                "SubsetSetMinusCommonRightMonotone",
                "공통 오른쪽 집합 차집합의 단조성",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
            OutputLanguage::Vietnamese => text(
                "SubsetSetMinusCommonRightMonotone",
                "Đơn điệu hiệu với tập phải chung",
                "`A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
            ),
        }
    }
}

impl SubsetCartComponentwiseBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubsetCartComponentwise",
            "Subset Cart Componentwise",
            "Componentwise: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "SubsetCartComponentwise",
            "笛卡尔积分量子集",
            "分量子集推出笛卡尔积子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "SubsetCartComponentwise",
            "笛卡兒積逐分量子集關係",
            "逐分量：`A $subset C`、`B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },
            OutputLanguage::French => {
        text(
            "SubsetCartComponentwise",
            "Inclusion cartésienne par composantes",
            "Composante par composante : `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },
            OutputLanguage::Russian => {
        text(
            "SubsetCartComponentwise",
            "Покомпонентное декартово включение",
            "Покомпонентно: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "SubsetCartComponentwise",
            "Inclusión cartesiana por componentes",
            "Por componentes: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "SubsetCartComponentwise",
            "احتواء ديكارتي بالمكونات",
            "بالمكونات: `A $subset C` و`B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "SubsetCartComponentwise",
            "直積の成分ごとの包含",
            "成分ごとに：`A $subset C`、`B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },
            OutputLanguage::Korean => {
        text(
            "SubsetCartComponentwise",
            "데카르트 곱의 성분별 포함",
            "성분별: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "SubsetCartComponentwise",
            "Tập con Descartes theo thành phần",
            "Theo thành phần: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    },

        }
    }
}

impl SubsetTransitivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SubsetTransitivity",
            "Subset Transitivity",
            "Transitivity through one known middle set: `A $subset B`, `B $subset C`",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SubsetTransitivity", "子集传递", "子集关系传递")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => {
        text(
            "SubsetTransitivity",
            "子集關係遞移性",
            "經一個已知中間集合的遞移性：`A $subset B`、`B $subset C`",
        )
    },
            OutputLanguage::French => {
        text(
            "SubsetTransitivity",
            "Transitivité de l'inclusion",
            "Transitivité via un ensemble intermédiaire connu : `A $subset B`, `B $subset C`",
        )
    },
            OutputLanguage::Russian => {
        text(
            "SubsetTransitivity",
            "Транзитивность включения",
            "Транзитивность через известное промежуточное множество: `A $subset B`, `B $subset C`",
        )
    },
            OutputLanguage::Spanish => {
        text(
            "SubsetTransitivity",
            "Transitividad de inclusión",
            "Transitividad por un conjunto intermedio conocido: `A $subset B`, `B $subset C`",
        )
    },
            OutputLanguage::Arabic => {
        text(
            "SubsetTransitivity",
            "تعدي الاحتواء الجزئي",
            "التعدي عبر مجموعة وسيطة معلومة: `A $subset B` و`B $subset C`",
        )
    },
            OutputLanguage::Japanese => {
        text(
            "SubsetTransitivity",
            "包含の推移性",
            "既知の中間集合を通る推移性：`A $subset B`、`B $subset C`",
        )
    },
            OutputLanguage::Korean => {
        text(
            "SubsetTransitivity",
            "부분집합 추이성",
            "알려진 중간 집합을 통한 추이성: `A $subset B`, `B $subset C`",
        )
    },
            OutputLanguage::Vietnamese => {
        text(
            "SubsetTransitivity",
            "Tính bắc cầu của tập con",
            "Tính bắc cầu qua tập trung gian đã biết: `A $subset B`, `B $subset C`",
        )
    },

        }
    }
}
