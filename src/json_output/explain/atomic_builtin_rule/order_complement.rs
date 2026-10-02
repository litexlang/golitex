use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::json_output::explain::fallback::BuiltinRuleText;
use crate::launch_command::OutputLanguage;
use super::text::text;

impl FromKnownOrderComplementBuiltinRuleProof {
    pub fn rule_id_and_message(&self, lang: OutputLanguage) -> BuiltinRuleText {
        match lang {
            OutputLanguage::English => text("FromKnownOrderComplement", "Known real-order complement", "A known negated comparison is equivalent to its complementary real order"),
            OutputLanguage::Chinese => text("FromKnownOrderComplement", "已知实数序的互补关系", "由已知比较事实及实数序的互补关系得到目标"),
        }
    }
}
