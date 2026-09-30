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
        text(
            "StandardSetSubset",
            "标准集子集",
            "标准数集之间的固定包含",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "SubsetUnionLeft",
            "左因子是并的子集",
            "左因子是并的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "SubsetUnionRight",
            "右因子是并的子集",
            "右因子是并的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "SubsetReflexivity",
            "子集自反",
            "任意集合是自身的子集",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
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
        text(
            "SubsetTransitivity",
            "子集传递",
            "子集关系传递",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
        }
    }
}

