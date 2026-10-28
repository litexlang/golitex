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

pub(crate) fn integer_range_cover_rule(
    rule: &str,
    language: crate::launch_command::OutputLanguage,
) -> BuiltinRuleText {
    use crate::launch_command::OutputLanguage::*;
    let message = match language {
        English => "The equality alternatives cover every integer in the known member's interval.",
        Chinese => "等号分支覆盖了已知成员所在整数区间的每个值。",
        ChineseTraditional => "等號分支覆蓋了已知成員所在整數區間的每個值。",
        French => "Les égalités couvrent tous les entiers de l’intervalle du membre connu.",
        Russian => "Варианты равенства покрывают все целые числа интервала известного элемента.",
        Spanish => "Las igualdades cubren cada entero del intervalo del miembro conocido.",
        Arabic => "تغطي بدائل المساواة جميع الأعداد الصحيحة في فترة العنصر المعروف.",
        Japanese => "等号の選択肢は既知の要素が属する整数区間の全ての値を覆います。",
        Korean => "등식 선택지가 알려진 원소의 정수 구간에 있는 모든 값을 포함합니다.",
        Vietnamese => "Các nhánh đẳng thức bao phủ mọi số nguyên trong khoảng của phần tử đã biết.",
    };
    text(rule, message)
}
