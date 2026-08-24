//! Recursion state for bounded builtin-rule proof search.

#[derive(Clone, Copy)]
pub struct BuiltinRuleSearchState {
    builtin_rule_depth: u8,
}

impl BuiltinRuleSearchState {
    pub fn initial() -> Self {
        Self {
            builtin_rule_depth: 0,
        }
    }

    pub fn can_apply_rule(&self) -> bool {
        self.builtin_rule_depth == 0
    }

    pub fn after_applying_rule(&self) -> Self {
        Self {
            builtin_rule_depth: self.builtin_rule_depth + 1,
        }
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/verify/proof_search/builtin_rule_state.rs"]
mod tests;
