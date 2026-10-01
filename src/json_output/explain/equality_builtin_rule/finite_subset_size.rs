use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_finite_subset_size::FiniteSetEqualFromSubsetSizeBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use super::text::text;

impl FiniteSetEqualFromSubsetSizeBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text(
                "FiniteSetEqualFromSubsetSize",
                "Equal finite subset cardinality",
                "A finite subset with the same cardinality as its containing set equals that set",
            ),
            OutputLanguage::Chinese => text(
                "FiniteSetEqualFromSubsetSize",
                "有限子集等大则相等",
                "有限子集与包含它的集合基数相等，因此两集合相等",
            ),
        }
    }
}
