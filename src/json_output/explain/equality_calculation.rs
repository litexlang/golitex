//! Localized text for EqualitySearchProofByCalculation.
//!
//! Internal variants (ClosedDecimal / Rational) only affect `message`;
//! JSON does not expose a `variant` field.

use super::fallback::BuiltinRuleText;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation;
use crate::launch_command::OutputLanguage;

pub fn explain_calculation(
    proof: &EqualitySearchProofByCalculation,
    lang: OutputLanguage,
) -> BuiltinRuleText {
    let rule_id = "Calculation";
    let (rule_name, message) = match (proof, lang) {
        (EqualitySearchProofByCalculation::ClosedDecimal { .. }, OutputLanguage::English) => (
            "Calculation".to_string(),
            "Both sides evaluate to the same number".to_string(),
        ),
        (EqualitySearchProofByCalculation::ClosedDecimal { .. }, OutputLanguage::Chinese) => (
            "计算".to_string(),
            "两边都算出同一个数".to_string(),
        ),
        (EqualitySearchProofByCalculation::Rational {}, OutputLanguage::English) => (
            "Calculation".to_string(),
            "Both sides are the same rational expression".to_string(),
        ),
        (EqualitySearchProofByCalculation::Rational {}, OutputLanguage::Chinese) => (
            "计算".to_string(),
            "两边是同一个有理式".to_string(),
        ),
    };
    BuiltinRuleText {
        rule_id,
        rule_name,
        message,
    }
}

#[cfg(test)]
mod tests {
    use super::explain_calculation;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation;
    use crate::launch_command::OutputLanguage;

    #[test]
    fn calculation_closed_decimal_english_and_chinese() {
        let proof = EqualitySearchProofByCalculation::ClosedDecimal {
            left_normal: "3".into(),
            right_normal: "3".into(),
        };
        let en = explain_calculation(&proof, OutputLanguage::English);
        assert_eq!(en.rule_id, "Calculation");
        assert_eq!(en.rule_name, "Calculation");
        assert_eq!(en.message, "Both sides evaluate to the same number");

        let zh = explain_calculation(&proof, OutputLanguage::Chinese);
        assert_eq!(zh.rule_id, "Calculation");
        assert_eq!(zh.rule_name, "计算");
        assert_eq!(zh.message, "两边都算出同一个数");
    }
}
