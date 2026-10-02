//! Calculation equality builtin explain.

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;

impl EqualitySearchProofByCalculation {
    pub fn rule_id_and_message_en(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedDecimal { .. } => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "Calculation".to_string(),
                message: "Both sides evaluate to the same number".to_string()
            },
            Self::Rational {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "Calculation".to_string(),
                message: "Both sides are the same rational expression".to_string()
            },
            Self::Complex {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "Calculation".to_string(),
                message: "Both sides are the same complex expression using i² = -1".to_string()
            }
        }
    }

    pub fn rule_id_and_message_zh(&self) -> BuiltinRuleText {
        match self {
            Self::ClosedDecimal { .. } => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "计算".to_string(),
                message: "两边都算出同一个数".to_string()
            },
            Self::Rational {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "计算".to_string(),
                message: "两边是同一个有理式".to_string()
            },
            Self::Complex {} => BuiltinRuleText {
                rule_id: "Calculation",
                rule_name: "计算".to_string(),
                message: "按 i² = -1 计算，两边是同一个复数表达式".to_string()
            }
        }
    }

    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => self.rule_id_and_message_en(),
            OutputLanguage::Chinese => self.rule_id_and_message_zh()
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
            right_normal: "3".into()
        };
        let en = proof.rule_id_and_message(OutputLanguage::English);
        assert_eq!(en.rule_name, "Calculation");
        assert_eq!(en.message, "Both sides evaluate to the same number");
        let zh = proof.rule_id_and_message(OutputLanguage::Chinese);
        assert_eq!(zh.rule_name, "计算");
        assert_eq!(zh.message, "两边都算出同一个数");
    }
}
