//! Calculation equality builtin explain.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl EqualitySearchProofByCalculation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedRational { .. } => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "Exact rational calculation".into(),
                message: "Both sides evaluate to the same exact rational number".into(),
            },
            Self::ClosedDecimal { .. } => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "Calculation".to_string(),
                message: "Both sides evaluate to the same number".to_string(),
            },
            Self::Rational {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "Calculation".to_string(),
                message: "Both sides are the same rational expression".to_string(),
            },
            Self::Complex {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "Calculation".to_string(),
                message: "Both sides are the same complex expression using i² = -1".to_string(),
            },
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedRational { .. } => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "精确有理数计算".into(),
                message: "两边都算出同一个精确有理数".into(),
            },
            Self::ClosedDecimal { .. } => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "计算".to_string(),
                message: "两边都算出同一个数".to_string(),
            },
            Self::Rational {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "计算".to_string(),
                message: "两边是同一个有理式".to_string(),
            },
            Self::Complex {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "计算".to_string(),
                message: "按 i² = -1 计算，两边是同一个复数表达式".to_string(),
            },
        }
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh(),
            OutputLanguage::ChineseTraditional => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "精確有理數計算".into(),
                    message: "兩邊都算出同一個精確有理數".into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "計算".to_string(),
                    message: "兩邊都算出同一個數".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "計算".to_string(),
                    message: "兩邊是同一個有理式".to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "計算".to_string(),
                    message: "按 i² = -1 計算，兩邊是同一個複數運算式".to_string(),
                },
            },
            OutputLanguage::French => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Calcul rationnel exact".into(),
                    message: "Les deux membres donnent le même nombre rationnel exact".into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Calcul".to_string(),
                    message: "Les deux membres donnent le même nombre".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Calcul".to_string(),
                    message: "Les deux membres sont la même expression rationnelle".to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Calcul".to_string(),
                    message: "Les deux membres sont la même expression complexe avec i² = -1"
                        .to_string(),
                },
            },
            OutputLanguage::Russian => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Точное рациональное вычисление".into(),
                    message: "Обе части вычисляются в одно и то же точное рациональное число"
                        .into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Вычисление".to_string(),
                    message: "Обе части вычисляются в одно и то же число".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Вычисление".to_string(),
                    message: "Обе части представляют одно и то же рациональное выражение"
                        .to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Вычисление".to_string(),
                    message:
                        "Обе части представляют одно и то же комплексное выражение при i² = -1"
                            .to_string(),
                },
            },
            OutputLanguage::Spanish => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Cálculo racional exacto".into(),
                    message: "Ambos lados dan el mismo número racional exacto".into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Cálculo".to_string(),
                    message: "Ambos lados dan el mismo número".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Cálculo".to_string(),
                    message: "Ambos lados son la misma expresión racional".to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Cálculo".to_string(),
                    message: "Ambos lados son la misma expresión compleja usando i² = -1"
                        .to_string(),
                },
            },
            OutputLanguage::Arabic => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "حساب نسبي دقيق".into(),
                    message: "يُقيَّم كلا الطرفين إلى العدد النسبي الدقيق نفسه".into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "حساب".to_string(),
                    message: "يُقيَّم كلا الطرفين إلى العدد نفسه".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "حساب".to_string(),
                    message: "الطرفان هما التعبير النسبي نفسه".to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "حساب".to_string(),
                    message: "الطرفان هما التعبير المركب نفسه باستخدام i² = -1".to_string(),
                },
            },
            OutputLanguage::Japanese => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "有理数の正確な計算".into(),
                    message: "両辺の計算結果は同じ正確な有理数です".into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "計算".to_string(),
                    message: "両辺の計算結果は同じ数です".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "計算".to_string(),
                    message: "両辺は同じ有理式です".to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "計算".to_string(),
                    message: "i² = -1 を用いると両辺は同じ複素数の式です".to_string(),
                },
            },
            OutputLanguage::Korean => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "정확한 유리수 계산".into(),
                    message: "양변의 계산 결과가 같은 정확한 유리수입니다".into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "계산".to_string(),
                    message: "양변의 계산 결과가 같은 수입니다".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "계산".to_string(),
                    message: "양변이 같은 유리식입니다".to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "계산".to_string(),
                    message: "i² = -1을 사용하면 양변이 같은 복소수 식입니다".to_string(),
                },
            },
            OutputLanguage::Vietnamese => match self {
                Self::ClosedRational { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Tính toán hữu tỉ chính xác".into(),
                    message: "Hai vế được tính ra cùng một số hữu tỉ chính xác".into(),
                },
                Self::ClosedDecimal { .. } => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Tính toán".to_string(),
                    message: "Hai vế được tính ra cùng một số".to_string(),
                },
                Self::Rational {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Tính toán".to_string(),
                    message: "Hai vế là cùng một biểu thức hữu tỉ".to_string(),
                },
                Self::Complex {} => BuiltinRuleText {
                    rule_id: "Calculation",
                    rule_name: "Tính toán".to_string(),
                    message: "Hai vế là cùng một biểu thức phức khi dùng i² = -1".to_string(),
                },
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::launch_command::OutputLanguage;

    #[test]
    fn calculation_closed_decimal_english_and_chinese() {
        let proof = EqualitySearchProofByCalculation::ClosedDecimal {
            left_normal: "3".into(),
            right_normal: "3".into(),
        };
        let en = proof.rule_id_and_message(OutputLanguage::English);
        assert_eq!(en.rule_name, "Calculation");
        assert_eq!(en.message, "Both sides evaluate to the same number");
        let zh = proof.rule_id_and_message(OutputLanguage::Chinese);
        assert_eq!(zh.rule_name, "计算");
        assert_eq!(zh.message, "两边都算出同一个数");
    }
}
