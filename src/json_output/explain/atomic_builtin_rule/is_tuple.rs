//! Leaf explain for atomic family group `is_tuple`.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_tuple::{
    IsTupleFactSearchProofByBuiltinRule,
    TupleLiteralBuiltinRuleProof,
};
use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::json_output::explain::text::text;

impl IsTupleFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_en(),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_zh(),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_zh_hant(),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_fr(),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_ru(),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_es(),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_ar(),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_ja(),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_ko(),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        match self {
            Self::TupleLiteral(p) => p.rule_name_and_message_vi(),
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
            Self::TupleLiteral(_) => None,
        }
    }
}

impl TupleLiteralBuiltinRuleProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Tuple Literal",
            "Verified by the tuple Literal builtin rule",
        )
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("元组字面量", "元组字面量形状成立")
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("元組字面值", "由元組字面值內建規則驗證")
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Tuple littéral",
            "Vérifié par la règle intégrée du tuple littéral",
        )
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Литерал кортежа",
            "Проверено встроенным правилом литерала кортежа",
        )
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Tupla literal",
            "Verificado por la regla incorporada de tupla literal",
        )
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text(
            "صف حرفي",
            "تم التحقق بقاعدة الصف الحرفي المدمجة",
        )
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "タプルリテラル",
            "タプルリテラルの組み込み規則で検証しました",
        )
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "튜플 리터럴",
            "튜플 리터럴 내장 규칙으로 검증했습니다",
        )
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Bộ literal",
            "Đã kiểm chứng bằng quy tắc tích hợp bộ literal",
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
