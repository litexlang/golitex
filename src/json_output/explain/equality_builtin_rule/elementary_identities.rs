//! The evidence enum also supplies per-variant reading rule identities.
use crate::prelude::*;

impl ElementaryIdentitySearchProofByBuiltinRule {
    pub fn rule_name_and_message(
        &self,
        language: OutputLanguage,
    ) -> crate::json_output::explain::BuiltinRuleText {
        super::native_operations::text(self.rule_id(), self.law(), language)
    }
}
