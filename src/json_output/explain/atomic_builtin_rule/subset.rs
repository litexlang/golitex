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
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl SubsetFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_en(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_en(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_en(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_en(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_en(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_en(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_en(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_en(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_en(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_en(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_en(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_en(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_en(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_en(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_en(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_en(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_en(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_en(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_zh(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_zh(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_zh(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_zh(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_zh(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_zh(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_zh(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_zh(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_zh(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_zh(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_zh(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_zh(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_zh(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_zh(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_zh(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_zh(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_zh(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_zh(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_zh_hant(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_zh_hant(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_zh_hant(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_zh_hant(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_zh_hant(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_zh_hant(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_zh_hant(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_zh_hant(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_zh_hant(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_zh_hant(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_zh_hant(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_zh_hant(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_zh_hant(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_zh_hant(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_zh_hant(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_zh_hant(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_zh_hant(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_zh_hant(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_fr(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_fr(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_fr(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_fr(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_fr(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_fr(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_fr(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_fr(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_fr(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_fr(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_fr(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_fr(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_fr(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_fr(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_fr(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_fr(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_fr(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_fr(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_ru(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_ru(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_ru(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_ru(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_ru(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_ru(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_ru(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_ru(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_ru(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_ru(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_ru(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_ru(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_ru(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_ru(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_ru(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_ru(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_ru(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_ru(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_es(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_es(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_es(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_es(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_es(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_es(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_es(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_es(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_es(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_es(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_es(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_es(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_es(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_es(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_es(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_es(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_es(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_es(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_ar(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_ar(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_ar(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_ar(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_ar(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_ar(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_ar(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_ar(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_ar(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_ar(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_ar(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_ar(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_ar(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_ar(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_ar(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_ar(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_ar(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_ar(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_ja(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_ja(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_ja(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_ja(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_ja(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_ja(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_ja(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_ja(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_ja(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_ja(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_ja(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_ja(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_ja(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_ja(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_ja(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_ja(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_ja(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_ja(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_ko(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_ko(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_ko(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_ko(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_ko(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_ko(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_ko(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_ko(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_ko(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_ko(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_ko(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_ko(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_ko(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_ko(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_ko(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_ko(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_ko(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_ko(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSubset(p) => p.rule_name_and_message_vi(),
            Self::IntersectSubsetLeft(p) => p.rule_name_and_message_vi(),
            Self::IntersectSubsetRight(p) => p.rule_name_and_message_vi(),
            Self::SubsetUnionLeft(p) => p.rule_name_and_message_vi(),
            Self::SubsetUnionRight(p) => p.rule_name_and_message_vi(),
            Self::SetMinusSubsetLeft(p) => p.rule_name_and_message_vi(),
            Self::RealIntervalSubsetReal(p) => p.rule_name_and_message_vi(),
            Self::SetBuilderSubsetOfParamSet(p) => p.rule_name_and_message_vi(),
            Self::SubsetReflexivity(p) => p.rule_name_and_message_vi(),
            Self::UnionSubsetFromBothOperands(p) => p.rule_name_and_message_vi(),
            Self::IntersectSubsetFromLeftUpperBound(p) => p.rule_name_and_message_vi(),
            Self::IntersectSubsetFromRightUpperBound(p) => p.rule_name_and_message_vi(),
            Self::ListSetSubsetFromMembers(p) => p.rule_name_and_message_vi(),
            Self::UnionSubsetFromComponentwise(p) => p.rule_name_and_message_vi(),
            Self::IntegerRangeSubsetNumericCarrier(p) => p.rule_name_and_message_vi(),
            Self::SubsetPowerSetMonotone(p) => p.rule_name_and_message_vi(),
            Self::SubsetSetMinusCommonRightMonotone(p) => p.rule_name_and_message_vi(),
            Self::SubsetCartComponentwise(p) => p.rule_name_and_message_vi(),
            Self::SubsetTransitivity(p) => p.rule_name_and_message_vi(),
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
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Standard Set Subset",
            "Fixed inclusion among standard number sets",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("标准集子集", "标准数集之间的固定包含")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "標準集合子集關係",
            "標準數集間的固定包含關係",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inclusion d'ensembles standards",
            "Inclusion fixe entre ensembles numériques standards",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Включение стандартных множеств",
            "Фиксированное включение стандартных числовых множеств",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión de conjuntos estándar",
            "Inclusión fija entre conjuntos numéricos estándar",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "احتواء مجموعات قياسية",
            "احتواء ثابت بين مجموعات الأعداد القياسية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "標準集合の包含関係",
            "標準的な数集合間の固定の包含関係",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "표준 집합 포함 관계",
            "표준 수 집합 사이의 고정된 포함 관계",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Quan hệ tập con chuẩn",
            "Bao hàm cố định giữa các tập số chuẩn",
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

impl IntersectSubsetLeftBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Intersect Subset Left",
            "The Intersect Subset Left rule establishes the following relation: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "交是左因子的子集",
            "交是左因子的子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "交集為左集合子集",
            "交集為左集合子集給出以下關係: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intersection incluse à gauche",
            "La règle « Intersection incluse à gauche » établit la relation suivante: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Пересечение включено в левое множество",
            "Правило «Пересечение включено в левое множество» устанавливает следующее соотношение: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intersección incluida a la izquierda",
            "La regla «Intersección incluida a la izquierda» establece la siguiente relación: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التقاطع جزئي من اليسار",
            "تثبت قاعدة «التقاطع جزئي من اليسار» العلاقة التالية: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "交差の左側への包含",
            "交差の左側への包含により次の関係が得られます: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "교집합의 왼쪽 포함",
            "교집합의 왼쪽 포함에 따라 다음 관계를 얻습니다: `intersect(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giao là tập con bên trái",
            "Quy tắc «Giao là tập con bên trái» thiết lập quan hệ sau: `intersect(A, B) $subset A`",
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

impl IntersectSubsetRightBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Intersect Subset Right",
            "The Intersect Subset Right rule establishes the following relation: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "交是右因子的子集",
            "交是右因子的子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "交集為右集合子集",
            "交集為右集合子集給出以下關係: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intersection incluse à droite",
            "La règle « Intersection incluse à droite » établit la relation suivante: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Пересечение включено в правое множество",
            "Правило «Пересечение включено в правое множество» устанавливает следующее соотношение: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intersección incluida a la derecha",
            "La regla «Intersección incluida a la derecha» establece la siguiente relación: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "التقاطع جزئي من اليمين",
            "تثبت قاعدة «التقاطع جزئي من اليمين» العلاقة التالية: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "交差の右側への包含",
            "交差の右側への包含により次の関係が得られます: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "교집합의 오른쪽 포함",
            "교집합의 오른쪽 포함에 따라 다음 관계를 얻습니다: `intersect(A, B) $subset B`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giao là tập con bên phải",
            "Quy tắc «Giao là tập con bên phải» thiết lập quan hệ sau: `intersect(A, B) $subset B`",
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

impl SubsetUnionLeftBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Subset Union Left",
            "The Subset Union Left rule establishes the following relation: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("左因子是并的子集", "左因子是并的子集")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "左集合為聯集子集",
            "左集合為聯集子集給出以下關係: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Opérande gauche inclus dans l'union",
            "La règle « Opérande gauche inclus dans l'union » établit la relation suivante: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Левое множество включено в объединение",
            "Правило «Левое множество включено в объединение» устанавливает следующее соотношение: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Operando izquierdo incluido en unión",
            "La regla «Operando izquierdo incluido en unión» establece la siguiente relación: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اليسار جزئي من الاتحاد",
            "تثبت قاعدة «اليسار جزئي من الاتحاد» العلاقة التالية: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "左集合の和集合への包含",
            "左集合の和集合への包含により次の関係が得られます: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "왼쪽 집합의 합집합 포함",
            "왼쪽 집합의 합집합 포함에 따라 다음 관계를 얻습니다: `A $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập trái là tập con của hợp",
            "Quy tắc «Tập trái là tập con của hợp» thiết lập quan hệ sau: `A $subset union(A, B)`",
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

impl SubsetUnionRightBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Subset Union Right",
            "The Subset Union Right rule establishes the following relation: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("右因子是并的子集", "右因子是并的子集")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "右集合為聯集子集",
            "右集合為聯集子集給出以下關係: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Opérande droit inclus dans l'union",
            "La règle « Opérande droit inclus dans l'union » établit la relation suivante: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Правое множество включено в объединение",
            "Правило «Правое множество включено в объединение» устанавливает следующее соотношение: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Operando derecho incluido en unión",
            "La regla «Operando derecho incluido en unión» establece la siguiente relación: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "اليمين جزئي من الاتحاد",
            "تثبت قاعدة «اليمين جزئي من الاتحاد» العلاقة التالية: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "右集合の和集合への包含",
            "右集合の和集合への包含により次の関係が得られます: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "오른쪽 집합의 합집합 포함",
            "오른쪽 집합의 합집합 포함에 따라 다음 관계를 얻습니다: `B $subset union(A, B)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập phải là tập con của hợp",
            "Quy tắc «Tập phải là tập con của hợp» thiết lập quan hệ sau: `B $subset union(A, B)`",
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

impl SetMinusSubsetLeftBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Set Minus Subset Left",
            "The Set Minus Subset Left rule establishes the following relation: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "差集是左因子的子集",
            "差集是左因子的子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "差集為左集合子集",
            "差集為左集合子集給出以下關係: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Différence incluse à gauche",
            "La règle « Différence incluse à gauche » établit la relation suivante: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Разность включена в левое множество",
            "Правило «Разность включена в левое множество» устанавливает следующее соотношение: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Diferencia incluida a la izquierda",
            "La regla «Diferencia incluida a la izquierda» establece la siguiente relación: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "الفرق جزئي من اليسار",
            "تثبت قاعدة «الفرق جزئي من اليسار» العلاقة التالية: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "差集合の左側への包含",
            "差集合の左側への包含により次の関係が得られます: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "차집합의 왼쪽 포함",
            "차집합의 왼쪽 포함에 따라 다음 관계를 얻습니다: `set_minus(A, B) $subset A`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Hiệu là tập con bên trái",
            "Quy tắc «Hiệu là tập con bên trái» thiết lập quan hệ sau: `set_minus(A, B) $subset A`",
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

impl RealIntervalSubsetRealBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Real Interval Subset Real",
            "Real intervals inhabit R",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "实区间是 R 的子集",
            "实区间是实数集的子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "實數區間為實數集子集",
            "實數區間包含於 R",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intervalle réel inclus dans les réels",
            "Les intervalles réels sont inclus dans R",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Вещественный интервал включён в вещественные",
            "Вещественные интервалы содержатся в R",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intervalo real incluido en los reales",
            "Los intervalos reales están incluidos en R",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فترة حقيقية جزئية من الأعداد الحقيقية",
            "الفترات الحقيقية محتواة في R",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "実数区間の実数集合への包含",
            "実数区間は R に含まれます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "실수 구간의 실수 집합 포함",
            "실수 구간은 R에 포함됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khoảng thực là tập con số thực",
            "Các khoảng thực nằm trong R",
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

impl SetBuilderSubsetOfParamSetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Set Builder Subset Of Param Set",
            "The Set Builder Subset Of Param Set rule establishes the following relation: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "集合构造子集于参数集",
            "集合构造式是参数集的子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "集合構造為參數集合子集",
            "集合構造為參數集合子集給出以下關係: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Ensemble défini en compréhension inclus dans son ensemble paramètre",
            "La règle « Ensemble défini en compréhension inclus dans son ensemble paramètre » établit la relation suivante: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Множество по условию включено в параметрическое множество",
            "Правило «Множество по условию включено в параметрическое множество» устанавливает следующее соотношение: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Conjunto por comprensión incluido en conjunto parámetro",
            "La regla «Conjunto por comprensión incluido en conjunto parámetro» establece la siguiente relación: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "المجموعة المبنية جزئية من مجموعة المعامل",
            "تثبت قاعدة «المجموعة المبنية جزئية من مجموعة المعامل» العلاقة التالية: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "内包表記集合のパラメータ集合への包含",
            "内包表記集合のパラメータ集合への包含により次の関係が得られます: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "조건제시 집합의 매개변수 집합 포함",
            "조건제시 집합의 매개변수 집합 포함에 따라 다음 관계를 얻습니다: `{x S: P…} $subset S`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập dựng là tập con của tập tham số",
            "Quy tắc «Tập dựng là tập con của tập tham số» thiết lập quan hệ sau: `{x S: P…} $subset S`",
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

impl SubsetReflexivityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Subset Reflexivity",
            "Reflexivity: `A $subset A`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("子集自反", "任意集合是自身的子集")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "子集關係自反性",
            "自反性：`A $subset A`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Réflexivité de l'inclusion",
            "Réflexivité : `A $subset A`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Рефлексивность включения",
            "Рефлексивность: `A $subset A`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Reflexividad de inclusión",
            "Reflexividad: `A $subset A`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انعكاسية الاحتواء الجزئي",
            "الانعكاسية: `A $subset A`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text("包含の反射性", "反射性：`A $subset A`")
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "부분집합 반사성",
            "반사성: `A $subset A`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính phản xạ của tập con",
            "Tính phản xạ: `A $subset A`",
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

impl UnionSubsetFromBothOperandsBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union Subset From Both Operands",
            "`A $subset S` and `B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "两边子集推出并是子集",
            "两边都是子集则其并也是子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由兩運算元得聯集子集",
            "`A $subset S` 與 `B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inclusion de l'union depuis les deux opérandes",
            "Si les deux ensembles sont contenus dans S, leur union est aussi contenue dans S: A ⊆ S ∧ B ⊆ S ⇒ A ∪ B ⊆ S",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Включение объединения по обоим операндам",
            "`A $subset S` и `B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión de unión desde ambos operandos",
            "La regla «Inclusión de unión desde ambos operandos» establece la siguiente relación: `A $subset S` y `B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "احتواء الاتحاد من المعاملين",
            "`A $subset S` و`B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "両被演算子から和集合の包含",
            "`A $subset S` かつ `B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "두 피연산자로 합집합 포함",
            "`A $subset S` 및 `B $subset S` ⇒ `union(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bao hàm hợp từ hai toán hạng",
            "`A $subset S` và `B $subset S` ⇒ `union(A, B) $subset S`",
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

impl IntersectSubsetFromLeftUpperBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Intersect Subset From Left Upper Bound",
            "The Intersect Subset From Left Upper Bound rule establishes the following relation: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "左上界推出交是子集",
            "左因子是子集则交也是子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "交集繼承左集合上界",
            "交集繼承左集合上界給出以下關係: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne d'inclusion de l'intersection depuis la gauche",
            "La règle « Borne d'inclusion de l'intersection depuis la gauche » établit la relation suivante: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Включение пересечения по левой верхней границе",
            "Правило «Включение пересечения по левой верхней границе» устанавливает следующее соотношение: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión de intersección por cota izquierda",
            "La regla «Inclusión de intersección por cota izquierda» establece la siguiente relación: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "احتواء التقاطع من الحد الأعلى الأيسر",
            "تثبت قاعدة «احتواء التقاطع من الحد الأعلى الأيسر» العلاقة التالية: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "左側の上界から交差の包含",
            "左側の上界から交差の包含により次の関係が得られます: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "왼쪽 상한으로 교집합 포함",
            "왼쪽 상한으로 교집합 포함에 따라 다음 관계를 얻습니다: `A $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bao hàm giao từ cận trên trái",
            "Quy tắc «Bao hàm giao từ cận trên trái» thiết lập quan hệ sau: `A $subset S` ⇒ `intersect(A, B) $subset S`",
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

impl IntersectSubsetFromRightUpperBoundBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Intersect Subset From Right Upper Bound",
            "The Intersect Subset From Right Upper Bound rule establishes the following relation: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "右上界推出交是子集",
            "右因子是子集则交也是子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "交集繼承右集合上界",
            "交集繼承右集合上界給出以下關係: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Borne d'inclusion de l'intersection depuis la droite",
            "La règle « Borne d'inclusion de l'intersection depuis la droite » établit la relation suivante: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Включение пересечения по правой верхней границе",
            "Правило «Включение пересечения по правой верхней границе» устанавливает следующее соотношение: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión de intersección por cota derecha",
            "La regla «Inclusión de intersección por cota derecha» establece la siguiente relación: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "احتواء التقاطع من الحد الأعلى الأيمن",
            "تثبت قاعدة «احتواء التقاطع من الحد الأعلى الأيمن» العلاقة التالية: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "右側の上界から交差の包含",
            "右側の上界から交差の包含により次の関係が得られます: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "오른쪽 상한으로 교집합 포함",
            "오른쪽 상한으로 교집합 포함에 따라 다음 관계를 얻습니다: `B $subset S` ⇒ `intersect(A, B) $subset S`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bao hàm giao từ cận trên phải",
            "Quy tắc «Bao hàm giao từ cận trên phải» thiết lập quan hệ sau: `B $subset S` ⇒ `intersect(A, B) $subset S`",
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

impl ListSetSubsetFromMembersBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "List Set Subset From Members",
            "`{a1, …, an} $subset S` from each `ai $in S`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "列表元素推出列表集是子集",
            "各元素属于则列表集是子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由成員關係得列表集合子集",
            "每個 `ai $in S` 推出 `{a1, …, an} $subset S`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inclusion d'ensemble liste par ses membres",
            "`{a1, …, an} $subset S` depuis chaque `ai $in S`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Включение списочного множества по элементам",
            "`{a1, …, an} $subset S` из каждого `ai $in S`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión de conjunto de lista por miembros",
            "`{a1, …, an} $subset S` a partir de cada `ai $in S`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "احتواء مجموعة قائمة من عناصرها",
            "`{a1, …, an} $subset S` من كل `ai $in S`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "要素の所属からリスト集合の包含",
            "各 `ai $in S` から `{a1, …, an} $subset S`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "원소 소속으로 목록 집합 포함",
            "각 `ai $in S`에서 `{a1, …, an} $subset S`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập danh sách là tập con từ phần tử",
            "`{a1, …, an} $subset S` từ mỗi `ai $in S`",
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

impl UnionSubsetFromComponentwiseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Union Subset From Componentwise",
            "`union(A, B) $subset union(C, D)` from componentwise subsets",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "分量子集推出并是子集",
            "分量子集推出并集子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "由逐分量關係得聯集子集",
            "逐分量子集關係推出 `union(A, B) $subset union(C, D)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inclusion de l'union par composantes",
            "`union(A, B) $subset union(C, D)` par les inclusions composante par composante",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Включение объединения покомпонентно",
            "`union(A, B) $subset union(C, D)` из покомпонентных включений",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión de unión por componentes",
            "`union(A, B) $subset union(C, D)` por inclusiones componente a componente",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "احتواء الاتحاد بالمكونات",
            "`union(A, B) $subset union(C, D)` من الاحتواء بالمكونات",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "成分ごとの関係から和集合の包含",
            "成分ごとの包含から `union(A, B) $subset union(C, D)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "성분별 관계로 합집합 포함",
            "성분별 부분집합에서 `union(A, B) $subset union(C, D)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bao hàm hợp theo thành phần",
            "`union(A, B) $subset union(C, D)` từ quan hệ tập con từng thành phần",
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

impl IntegerRangeSubsetNumericCarrierBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Integer Range Subset Numeric Carrier",
            "Integer `range` / `closed_range` sits in its numeric carrier",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "整数区间属于数值载体",
            "整数区间落在其数值载体中",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "整數區間為數值載體的子集",
            "整數 `range` 或 `closed_range` 包含於其數值載體",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Intervalle entier inclus dans son ensemble numérique porteur",
            "Un `range` ou `closed_range` entier est inclus dans son ensemble numérique porteur",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Целочисленный интервал является подмножеством числового носителя",
            "Целочисленный `range` или `closed_range` содержится в числовом носителе",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Intervalo entero subconjunto de portador numérico",
            "El `range` o `closed_range` entero está incluido en su portador numérico",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "فترة صحيحة جزئية من المجموعة الحاملة العددية",
            "`range` أو `closed_range` الصحيح محتوى في مجموعته الحاملة العددية",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "整数区間の数値台集合への包含",
            "整数の `range` または `closed_range` は数値台集合に含まれます",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "정수 구간의 수치 바탕 집합 포함",
            "정수 `range` 또는 `closed_range`는 수치 바탕 집합에 포함됩니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Khoảng nguyên là tập con của tập nền số",
            "`range` hoặc `closed_range` nguyên nằm trong tập nền số của nó",
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

impl SubsetPowerSetMonotoneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Subset Power Set Monotone",
            "The Subset Power Set Monotone rule establishes the following relation: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "幂集对子集单调",
            "子集关系在幂集上单调",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "冪集子集單調性",
            "冪集子集單調性給出以下關係: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie d'inclusion de l'ensemble des parties",
            "La règle « Monotonie d'inclusion de l'ensemble des parties » établit la relation suivante: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Монотонность включения множества подмножеств",
            "Правило «Монотонность включения множества подмножеств» устанавливает следующее соотношение: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía de inclusión del conjunto potencia",
            "La regla «Monotonía de inclusión del conjunto potencia» establece la siguiente relación: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة احتواء مجموعة القوى",
            "تثبت قاعدة «رتابة احتواء مجموعة القوى» العلاقة التالية: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "べき集合の包含の単調性",
            "べき集合の包含の単調性により次の関係が得られます: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "멱집합 포함 단조성",
            "멱집합 포함 단조성에 따라 다음 관계를 얻습니다: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đơn điệu tập con của tập lũy thừa",
            "Quy tắc «Đơn điệu tập con của tập lũy thừa» thiết lập quan hệ sau: `A $subset B` ⇒ `power_set(A) $subset power_set(B)`",
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

impl SubsetSetMinusCommonRightMonotoneBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Subset Set Minus Common Right Monotone",
            "The Subset Set Minus Common Right Monotone rule establishes the following relation: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "同右差集对子集单调",
            "同右差集保持子集关系",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "差集共用右集合的子集單調性",
            "差集共用右集合的子集單調性給出以下關係: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Monotonie de différence à opérande droit commun",
            "La règle « Monotonie de différence à opérande droit commun » établit la relation suivante: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Монотонность разности с общим правым множеством",
            "Правило «Монотонность разности с общим правым множеством» устанавливает следующее соотношение: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Monotonía de diferencia con operando derecho común",
            "La regla «Monotonía de diferencia con operando derecho común» establece la siguiente relación: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "رتابة الفرق بمجموعة يمنى مشتركة",
            "تثبت قاعدة «رتابة الفرق بمجموعة يمنى مشتركة» العلاقة التالية: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "共通の右集合を持つ差集合の単調性",
            "共通の右集合を持つ差集合の単調性により次の関係が得られます: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "공통 오른쪽 집합 차집합의 단조성",
            "공통 오른쪽 집합 차집합의 단조성에 따라 다음 관계를 얻습니다: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Đơn điệu hiệu với tập phải chung",
            "Quy tắc «Đơn điệu hiệu với tập phải chung» thiết lập quan hệ sau: `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`",
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

impl SubsetCartComponentwiseBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Subset Cart Componentwise",
            "Componentwise: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "笛卡尔积分量子集",
            "分量子集推出笛卡尔积子集",
        )
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "笛卡兒積逐分量子集關係",
            "逐分量：`A $subset C`、`B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Inclusion cartésienne par composantes",
            "Composante par composante : `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Покомпонентное декартово включение",
            "Покомпонентно: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Inclusión cartesiana por componentes",
            "Por componentes: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "احتواء ديكارتي بالمكونات",
            "بالمكونات: `A $subset C` و`B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "直積の成分ごとの包含",
            "成分ごとに：`A $subset C`、`B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "데카르트 곱의 성분별 포함",
            "성분별: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập con Descartes theo thành phần",
            "Theo thành phần: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`",
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

impl SubsetTransitivityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Subset Transitivity",
            "Transitivity through one known middle set: `A $subset B`, `B $subset C`",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("子集传递", "子集关系传递")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text(
            "子集關係遞移性",
            "經一個已知中間集合的遞移性：`A $subset B`、`B $subset C`",
        )
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Transitivité de l'inclusion",
            "Transitivité via un ensemble intermédiaire connu : `A $subset B`, `B $subset C`",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Транзитивность включения",
            "Транзитивность через известное промежуточное множество: `A $subset B`, `B $subset C`",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Transitividad de inclusión",
            "Transitividad por un conjunto intermedio conocido: `A $subset B`, `B $subset C`",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "تعدي الاحتواء الجزئي",
            "التعدي عبر مجموعة وسيطة معلومة: `A $subset B` و`B $subset C`",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "包含の推移性",
            "既知の中間集合を通る推移性：`A $subset B`、`B $subset C`",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "부분집합 추이성",
            "알려진 중간 집합을 통한 추이성: `A $subset B`, `B $subset C`",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính bắc cầu của tập con",
            "Tính bắc cầu qua tập trung gian đã biết: `A $subset B`, `B $subset C`",
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
