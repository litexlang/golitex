use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof as P;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

pub(super) fn explain(proof: &P, lang: OutputLanguage) -> BuiltinRuleText {
    let (en, zh, message_en, message_zh) = match proof {
        T::PeriodicTrig(_) => ("Exact periodic trigonometric value", "精确周期三角值", "Reduce the exact pi coefficient using checked integer periods", "依据已验证的整数周期归约精确 pi 系数"),
        T::NumericComplexModulus(_) => ("Exact numeric complex modulus", "数字复数模长精确计算", "Compute exact real/imaginary coordinates and take the nonnegative principal root", "精确计算实部与虚部并取非负主根"),
        P::AbsZeroArgument(_) => (
            "Zero absolute value",
            "绝对值为零",
            "A real number whose absolute value is zero equals zero",
            "实数的绝对值为零时，该实数等于零",
        ),
        P::FloorNegation(_) => (
            "Floor of a negation",
            "取负后的向下取整",
            "floor(-x) = -ceil(x) for real x",
            "实数 x 满足 floor(-x) = -ceil(x)",
        ),
        P::CeilNegation(_) => (
            "Ceiling of a negation",
            "取负后的向上取整",
            "ceil(-x) = -floor(x) for real x",
            "实数 x 满足 ceil(-x) = -floor(x)",
        ),
        P::FloorIntegerTranslation(_) => (
            "Integer translation of floor",
            "向下取整的整数平移",
            "An integer shift commutes with floor",
            "经验证的整数位移可移出 floor",
        ),
        P::CeilIntegerTranslation(_) => (
            "Integer translation of ceiling",
            "向上取整的整数平移",
            "An integer shift commutes with ceiling",
            "经验证的整数位移可移出 ceil",
        ),
        P::MinMaxAbsorption(_) => (
            "Minimum absorbs maximum",
            "最小值吸收最大值",
            "min(a, max(a, b)) = a for real operands",
            "实数操作数满足 min(a, max(a, b)) = a",
        ),
        P::MaxMinAbsorption(_) => (
            "Maximum absorbs minimum",
            "最大值吸收最小值",
            "max(a, min(a, b)) = a for real operands",
            "实数操作数满足 max(a, min(a, b)) = a",
        ),
        P::LcmZero(_) => (
            "Zero argument of lcm",
            "lcm 的零参数",
            "The least common multiple is zero when either integer argument is zero",
            "lcm 的任一整数参数为零时，结果为零",
        ),
    };
    let (name, message) = match lang {
        OutputLanguage::English => (en, message_en),
        OutputLanguage::Chinese => (zh, message_zh),
    };
    BuiltinRuleText {
        rule_id: proof.rule_id(),
        rule_name: name.into(),
        message: message.into(),
    }
}

pub(super) fn trig_complex(
    proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof,
    lang: OutputLanguage,
) -> BuiltinRuleText {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof as T;
    let (en, zh, message_en, message_zh) = match proof {
        T::SinDifference => ("Sine difference formula", "正弦差角公式", "sin(x-y)=sin(x)cos(y)-cos(x)sin(y) for checked real arguments", "经验证的实数参数满足 sin(x-y)=sin(x)cos(y)-cos(x)sin(y)"),
        T::CosDifference => ("Cosine difference formula", "余弦差角公式", "cos(x-y)=cos(x)cos(y)+sin(x)sin(y) for checked real arguments", "经验证的实数参数满足 cos(x-y)=cos(x)cos(y)+sin(x)sin(y)"),
        T::ComplexModulusProduct => ("Multiplicativity of complex modulus", "复数模的乘法公式", "C_abs(z*w)=C_abs(z)*C_abs(w) for checked complex arguments", "经验证的复数参数满足 C_abs(z*w)=C_abs(z)*C_abs(w)"),
        _ => ("Trigonometric or complex coordinate identity", "三角或复坐标恒等式", "Apply the trigonometric or complex coordinate identity with checked premises", "依据已验证的前提应用三角或复坐标恒等式"),
    };
    let (name, message) = match lang {
        OutputLanguage::English => (en, message_en), OutputLanguage::Chinese => (zh, message_zh),
    };
    BuiltinRuleText { rule_id: proof.rule_id(), rule_name: name.into(), message: message.into() }
}
