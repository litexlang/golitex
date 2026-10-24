/// Localized builtin-rule name and explanation for Normal JSON.
/// The owning proof type or enum variant identifies the rule.
pub struct BuiltinRuleText {
    pub rule_name: String,
    pub message: String,
}

pub(super) fn text(rule_name: &str, message: &str) -> BuiltinRuleText {
    BuiltinRuleText {
        rule_name: rule_name.to_string(),
        message: message.to_string(),
    }
}

pub(crate) fn native_matrix_rule(
    rule: &str,
    law: &str,
    language: crate::launch_command::OutputLanguage,
) -> super::BuiltinRuleText {
    use crate::launch_command::OutputLanguage::*;
    let prefix = match language {
        English => "Matrix domain and defining rule checked",
        Chinese => "矩阵定义域及定义规则已检查",
        ChineseTraditional => "矩陣定義域及定義規則已檢查",
        French => "Domaine matriciel et règle de définition vérifiés",
        Russian => "Область матрицы и определяющее правило проверены",
        Spanish => "Dominio matricial y regla de definición verificados",
        Arabic => "تم التحقق من مجال المصفوفة وقاعدة التعريف",
        Japanese => "行列の定義域と定義規則を確認済み",
        Korean => "행렬 정의역과 정의 규칙을 확인했습니다",
        Vietnamese => "Đã kiểm tra miền ma trận và quy tắc định nghĩa",
    };
    super::BuiltinRuleText {
        rule_name: rule.into(),
        message: format!("{prefix}: {law}"),
    }
}
