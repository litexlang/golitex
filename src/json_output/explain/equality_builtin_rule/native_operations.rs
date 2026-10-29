use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
pub(super) fn text(rule: &str, law: &str, language: OutputLanguage) -> BuiltinRuleText {
    let prefix = match language {
        OutputLanguage::English => "Conditions and identity",
        OutputLanguage::Chinese => "适用条件与恒等关系",
        OutputLanguage::ChineseTraditional => "兩邊及定義域條件均已檢查",
        OutputLanguage::French => "Les deux membres et leurs domaines sont vérifiés",
        OutputLanguage::Russian => "Обе части и условия области определения проверены",
        OutputLanguage::Spanish => "Ambos miembros y sus dominios están verificados",
        OutputLanguage::Arabic => "تم التحقق من الطرفين وشروط المجال",
        OutputLanguage::Japanese => "両辺と定義域の条件を確認済み",
        OutputLanguage::Korean => "양변과 정의역 조건을 확인했습니다",
        OutputLanguage::Vietnamese => "Hai vế và điều kiện miền xác định đã được kiểm tra",
    };
    BuiltinRuleText {
        rule_name: rule.into(),
        message: format!("{prefix}: {law}"),
    }
}
