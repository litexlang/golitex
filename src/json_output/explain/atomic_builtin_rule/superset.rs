//! Leaf explain for atomic family group `superset`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::superset::{
    StandardSetSupersetBuiltinRuleProof,
    SupersetFactSearchProofByBuiltinRule,
    SupersetReflexivityBuiltinRuleProof,
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl SupersetFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_en(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_zh(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_zh_hant(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_fr(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_ru(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_es(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_ar(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_ja(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_ko(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_name_and_message_vi(),
            Self::SupersetReflexivity(p) => p.rule_name_and_message_vi(),
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
            Self::StandardSetSuperset(_) => None,
            Self::SupersetReflexivity(_) => None,
        }
    }
}

impl StandardSetSupersetBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Standard Set Superset",
            "Verified by the standard Set Superset builtin rule",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("标准集超集", "标准数集之间的固定超集关系")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("標準集合包含", "由標準集合包含內建規則驗證")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Sur-ensemble standard",
            "Vérifié par la règle intégrée de sur-ensemble standard",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Стандартное надмножество",
            "Проверено встроенным правилом стандартного надмножества",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Superconjunto estándar",
            "Verificado por la regla incorporada de superconjunto estándar",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "مجموعة فوقية قياسية",
            "تم التحقق بقاعدة المجموعة الفوقية القياسية المدمجة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "標準集合の包含",
            "標準集合の包含の組み込み規則で検証しました",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text("표준 상위집합", "표준 상위집합 내장 규칙으로 검증했습니다")
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tập cha chuẩn",
            "Đã kiểm chứng bằng quy tắc tích hợp tập cha chuẩn",
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

impl SupersetReflexivityBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Superset Reflexivity",
            "Verified by the superset Reflexivity builtin rule",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("超集自反", "任意集合是自身的超集")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("包含關係自反性", "由包含關係自反性內建規則驗證")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Réflexivité du sur-ensemble",
            "Vérifié par la règle intégrée de réflexivité du sur-ensemble",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Рефлексивность надмножества",
            "Проверено встроенным правилом рефлексивности надмножества",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Reflexividad de superconjunto",
            "Verificado por la regla incorporada de reflexividad de superconjunto",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "انعكاسية الاحتواء",
            "تم التحقق بقاعدة انعكاسية الاحتواء المدمجة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "包含関係の反射性",
            "包含関係の反射性の組み込み規則で検証しました",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "상위집합 관계의 반사성",
            "상위집합 반사성 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Tính phản xạ của quan hệ tập cha",
            "Đã kiểm chứng bằng quy tắc tích hợp tính phản xạ của tập cha",
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
