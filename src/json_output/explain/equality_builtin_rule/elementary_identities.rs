//! The evidence enum also supplies per-variant reading rule identities.
use crate::json_output::explain::BuiltinRuleText;
use crate::prelude::*;

impl ElementaryIdentitySearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("Both sides and domain guards checked: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("两边及定义域条件均已检查: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("兩邊及定義域條件均已檢查: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Les deux membres et leurs domaines sont vérifiés: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Обе части и условия области определения проверены: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Ambos miembros y sus dominios están verificados: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("تم التحقق من الطرفين وشروط المجال: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("両辺と定義域の条件を確認済み: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!("양변과 정의역 조건을 확인했습니다: {}", self.law()),
        }
    }

    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: self.rule_id().into(),
            message: format!(
                "Hai vế và điều kiện miền xác định đã được kiểm tra: {}",
                self.law()
            ),
        }
    }

    pub fn rule_name_and_message(&self, language: OutputLanguage) -> BuiltinRuleText {
        match language {
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
