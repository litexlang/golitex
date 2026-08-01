#[derive(Clone, Copy)]
pub struct BuiltinRuleVerifyState {
    builtin_rule_depth: u8,
}

impl BuiltinRuleVerifyState {
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
mod tests {
    use super::*;

    #[test]
    fn root_state_allows_one_builtin_rule() {
        let state = BuiltinRuleVerifyState::new();
        assert!(state.can_apply_builtin_rule());
    }

    #[test]
    fn child_state_does_not_allow_another_builtin_rule() {
        let root = BuiltinRuleVerifyState::new();
        let child = root.after_applying_builtin_rule();
        assert!(!child.can_apply_builtin_rule());
        assert!(root.can_apply_builtin_rule());
    }
}
