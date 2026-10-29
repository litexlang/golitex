//! Mathematical comments for the individual scalar identity certificates.
use super::BuiltinRuleText;
use super::text::text;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_extra::*;
impl SqrtProductFromKnownArgumentProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Square root of a product",
            "For nonnegative real a,b and c=a·b, √c=√a·√b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("乘积的平方根", "对非负实数 a、b，若 c=a·b，则 √c=√a·√b。")
    }
}
impl SqrtQuotientFromKnownArgumentProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Square root of a quotient",
            "For real a≥0, b>0 and c=a/b, √c=√a/√b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("商的平方根", "对实数 a≥0、b>0，若 c=a/b，则 √c=√a/√b。")
    }
}
impl ArcsinFromKnownSineProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Identify the principal inverse sine",
            "If x=sin(y) and −π/2≤y≤π/2, then arcsin(x)=y. The principal interval is essential.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "确定反正弦主值",
            "若 x=sin(y) 且 −π/2≤y≤π/2，则 arcsin(x)=y；主值区间条件不可省略。",
        )
    }
}
impl RealLogFromKnownPowerProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Logarithm from a known real power",
            "For a>0, a≠1 and real y, a^y=x implies log(a,x)=y.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "由已知实数幂确定对数",
            "若 a>0、a≠1，y 为实数，则 a^y=x 推出 log(a,x)=y。",
        )
    }
}
impl PositivePowerLogInverseProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Power and logarithm are inverse",
            "For a>0, a≠1 and x>0, a^log(a,x)=x.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("幂与对数互逆", "若 a>0、a≠1 且 x>0，则 a^log(a,x)=x。")
    }
}
impl PositivePowerReciprocalRootProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Recover a positive number from its power",
            "For x>0 and n ∈ ℕ+, (x^n)^(1/n)=x.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text("由幂恢复正数", "若 x>0 且 n ∈ ℕ+，则 (x^n)^(1/n)=x。")
    }
}
impl PositiveIntegerPowerInjectiveProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Injectivity of a nonzero integer power on positive reals",
            "For a,b>0 and nonzero integer n, a^n=b^n implies a=b.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "非零整数幂在正实数上的单射性",
            "若 a,b>0，n 为非零整数，则 a^n=b^n 推出 a=b。",
        )
    }
}
impl NestedRemainderUnitProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        text(
            "Remainder modulo one",
            "For integers a and nonzero m, (a mod m) mod 1=a mod 1=0.",
        )
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        text(
            "模一的余数",
            "对整数 a 与非零整数 m，(a mod m) mod 1=a mod 1=0。",
        )
    }
}
impl ScalarExtraEqualityProof {
    pub fn rule_name_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::SqrtProductFromKnownArgument(proof) => proof.rule_name_and_message_en(),
            Self::SqrtQuotientFromKnownArgument(proof) => proof.rule_name_and_message_en(),
            Self::ArcsinFromKnownSine(proof) => proof.rule_name_and_message_en(),
            Self::RealLogFromKnownPower(proof) => proof.rule_name_and_message_en(),
            Self::PositivePowerLogInverse(proof) => proof.rule_name_and_message_en(),
            Self::PositivePowerReciprocalRoot(proof) => proof.rule_name_and_message_en(),
            Self::PositiveIntegerPowerInjective(proof) => proof.rule_name_and_message_en(),
            Self::NestedRemainderUnit(proof) => proof.rule_name_and_message_en(),
        }
    }
    pub fn rule_name_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::SqrtProductFromKnownArgument(proof) => proof.rule_name_and_message_zh(),
            Self::SqrtQuotientFromKnownArgument(proof) => proof.rule_name_and_message_zh(),
            Self::ArcsinFromKnownSine(proof) => proof.rule_name_and_message_zh(),
            Self::RealLogFromKnownPower(proof) => proof.rule_name_and_message_zh(),
            Self::PositivePowerLogInverse(proof) => proof.rule_name_and_message_zh(),
            Self::PositivePowerReciprocalRoot(proof) => proof.rule_name_and_message_zh(),
            Self::PositiveIntegerPowerInjective(proof) => proof.rule_name_and_message_zh(),
            Self::NestedRemainderUnit(proof) => proof.rule_name_and_message_zh(),
        }
    }
}
