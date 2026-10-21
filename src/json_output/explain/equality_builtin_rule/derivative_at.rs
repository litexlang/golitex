use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_derivative::DerivativeSelectedValueProof;
use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::explain::text::text;
use crate::launch_command::OutputLanguage;
impl DerivativeSelectedValueProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Selected derivative",
            "A proved derivative candidate determines the selected value.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("导数选值", "已经证明的导数候选决定导数取值。")
    }
    pub fn rule_name_and_message_zh_hant(&self) -> BuiltinRuleText {
        text("導數選值", "已經證明的導數候選決定導數取值。")
    }
    pub fn rule_name_and_message_fr(&self) -> BuiltinRuleText {
        text(
            "Dérivée sélectionnée",
            "Un candidat de dérivée démontré détermine la valeur sélectionnée.",
        )
    }
    pub fn rule_name_and_message_ru(&self) -> BuiltinRuleText {
        text(
            "Выбранная производная",
            "Доказанное значение производной определяет выбранное значение.",
        )
    }
    pub fn rule_name_and_message_es(&self) -> BuiltinRuleText {
        text(
            "Derivada seleccionada",
            "Un candidato de derivada demostrado determina el valor seleccionado.",
        )
    }
    pub fn rule_name_and_message_ar(&self) -> BuiltinRuleText {
        text("قيمة المشتقة", "تحدد المشتقة المثبتة القيمة المختارة.")
    }
    pub fn rule_name_and_message_ja(&self) -> BuiltinRuleText {
        text(
            "導関数の選択値",
            "証明済みの微分係数候補が選択値を決定します。",
        )
    }
    pub fn rule_name_and_message_ko(&self) -> BuiltinRuleText {
        text(
            "미분계수 선택값",
            "증명된 미분계수 후보가 선택값을 결정합니다.",
        )
    }
    pub fn rule_name_and_message_vi(&self) -> BuiltinRuleText {
        text(
            "Giá trị đạo hàm",
            "Ứng viên đạo hàm đã chứng minh xác định giá trị được chọn.",
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
