#[derive(Clone, Copy)]
pub struct UseBuiltinRuleVerifyState {
    builtin_rule_depth: u8,
}

impl UseBuiltinRuleVerifyState {
    pub fn new() -> Self {
        Self {
            builtin_rule_depth: 0,
        }
    }

    pub fn can_apply_builtin_rule(&self) -> bool {
        self.builtin_rule_depth == 0
    }

    pub fn after_applying_builtin_rule(&self) -> Self {
        Self {
            builtin_rule_depth: self.builtin_rule_depth + 1,
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/verify/builtin_rule_verify_state/tests.rs"]
mod tests;
