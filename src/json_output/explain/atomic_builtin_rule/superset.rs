//! Leaf explain for atomic family group `superset`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::superset::{
    StandardSetSupersetBuiltinRuleProof,
    SupersetFactSearchProofByBuiltinRule,
    SupersetReflexivityBuiltinRuleProof,
};
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use super::text::text;

impl SupersetFactSearchProofByBuiltinRule {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match self {
            Self::StandardSetSuperset(p) => p.rule_id_and_message(lang),
            Self::SupersetReflexivity(p) => p.rule_id_and_message(lang),
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
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "StandardSetSuperset",
            "Standard Set Superset",
            "Verified by the standard Set Superset builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "StandardSetSuperset",
            "标准集超集",
            "标准数集之间的固定超集关系",
        )
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "StandardSetSuperset",
                "標準集合包含",
                "由標準集合包含內建規則驗證",
            ),
            OutputLanguage::French => text(
                "StandardSetSuperset",
                "Sur-ensemble standard",
                "Vérifié par la règle intégrée de sur-ensemble standard",
            ),
            OutputLanguage::Russian => text(
                "StandardSetSuperset",
                "Стандартное надмножество",
                "Проверено встроенным правилом стандартного надмножества",
            ),
            OutputLanguage::Spanish => text(
                "StandardSetSuperset",
                "Superconjunto estándar",
                "Verificado por la regla incorporada de superconjunto estándar",
            ),
            OutputLanguage::Arabic => text(
                "StandardSetSuperset",
                "مجموعة فوقية قياسية",
                "تم التحقق بقاعدة المجموعة الفوقية القياسية المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "StandardSetSuperset",
                "標準集合の包含",
                "標準集合の包含の組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "StandardSetSuperset",
                "표준 상위집합",
                "표준 상위집합 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "StandardSetSuperset",
                "Tập cha chuẩn",
                "Đã kiểm chứng bằng quy tắc tích hợp tập cha chuẩn",
            ),
        }
    }
}

impl SupersetReflexivityBuiltinRuleProof {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        text(
            "SupersetReflexivity",
            "Superset Reflexivity",
            "Verified by the superset Reflexivity builtin rule",
        )
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        text("SupersetReflexivity", "超集自反", "任意集合是自身的超集")
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => text(
                "SupersetReflexivity",
                "包含關係自反性",
                "由包含關係自反性內建規則驗證",
            ),
            OutputLanguage::French => text(
                "SupersetReflexivity",
                "Réflexivité du sur-ensemble",
                "Vérifié par la règle intégrée de réflexivité du sur-ensemble",
            ),
            OutputLanguage::Russian => text(
                "SupersetReflexivity",
                "Рефлексивность надмножества",
                "Проверено встроенным правилом рефлексивности надмножества",
            ),
            OutputLanguage::Spanish => text(
                "SupersetReflexivity",
                "Reflexividad de superconjunto",
                "Verificado por la regla incorporada de reflexividad de superconjunto",
            ),
            OutputLanguage::Arabic => text(
                "SupersetReflexivity",
                "انعكاسية الاحتواء",
                "تم التحقق بقاعدة انعكاسية الاحتواء المدمجة",
            ),
            OutputLanguage::Japanese => text(
                "SupersetReflexivity",
                "包含関係の反射性",
                "包含関係の反射性の組み込み規則で検証しました",
            ),
            OutputLanguage::Korean => text(
                "SupersetReflexivity",
                "상위집합 관계의 반사성",
                "상위집합 반사성 내장 규칙으로 검증했습니다",
            ),
            OutputLanguage::Vietnamese => text(
                "SupersetReflexivity",
                "Tính phản xạ của quan hệ tập cha",
                "Đã kiểm chứng bằng quy tắc tích hợp tính phản xạ của tập cha",
            ),
        }
    }
}
