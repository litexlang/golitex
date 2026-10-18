use super::super::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use crate::runtime::FactId;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::dvd::DvdFactSearchProofByBuiltinRule;

impl DvdFactSearchProofByBuiltinRule {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Divisibility: {}", self.rule_id()),
            message: format!(
                "Checked integer divisibility rule; domains are verified. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("整除: {}", self.rule_id()),
            message: format!("已检查整数整除性质及其定义域条件。 {}", self.law()),
        }
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("整除性: {}", self.rule_id()),
            message: format!("已檢查整數整除性質及其定義域條件。 {}", self.law()),
        }
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Divisibilité: {}", self.rule_id()),
            message: format!(
                "Propriété de divisibilité entière vérifiée avec ses conditions de domaine. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Делимость: {}", self.rule_id()),
            message: format!(
                "Проверено свойство целочисленной делимости и условия области определения. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Divisibilidad: {}", self.rule_id()),
            message: format!(
                "Propiedad de divisibilidad entera comprobada con sus condiciones de dominio. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("القابلية للقسمة: {}", self.rule_id()),
            message: format!(
                "تم التحقق من خاصية قسمة الأعداد الصحيحة وشروط مجالها. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("整除性質: {}", self.rule_id()),
            message: format!("整数の整除性と定義域の条件を検証しました。 {}", self.law()),
        }
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("나눗셈 관계: {}", self.rule_id()),
            message: format!(
                "정수의 나눗셈 관계와 정의역 조건을 검증했습니다. {}",
                self.law()
            ),
        }
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        BuiltinRuleText {
            rule_name: format!("Tính chia hết: {}", self.rule_id()),
            message: format!(
                "Đã kiểm tra tính chia hết của số nguyên và các điều kiện miền xác định. {}",
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
    pub fn cite_fact_id(&self) -> Option<FactId> {
        None
    }
}
