use crate::json_output::explain::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

pub(super) fn add_zero_from_equalities_text(
    rule_name: &str,
    language: OutputLanguage,
) -> BuiltinRuleText {
    let message = match language {
        OutputLanguage::English => {
            "Use the checked zero summand and equality of the remaining summand"
        }
        OutputLanguage::Chinese => "用已验证的零加数和另一加数的等式证明加法结果",
        OutputLanguage::ChineseTraditional => "用已驗證的零加數和另一加數的等式證明加法結果",
        OutputLanguage::French => "Utiliser le terme nul vérifié et l'égalité du terme restant",
        OutputLanguage::Russian => {
            "Использовать доказанное нулевое слагаемое и равенство другого слагаемого"
        }
        OutputLanguage::Spanish => "Usar el sumando nulo verificado y la igualdad del otro sumando",
        OutputLanguage::Arabic => "استخدام الحد الصفري المثبت ومساواة الحد الآخر",
        OutputLanguage::Japanese => "検証済みのゼロ項と残りの項の等式を用いる",
        OutputLanguage::Korean => "검증된 영 항과 나머지 항의 등식을 사용",
        OutputLanguage::Vietnamese => {
            "Dùng số hạng bằng không đã kiểm chứng và đẳng thức của số hạng còn lại"
        }
    };
    BuiltinRuleText {
        rule_name: rule_name.into(),
        message: message.into(),
    }
}
