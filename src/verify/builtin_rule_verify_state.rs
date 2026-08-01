pub struct BuiltinRuleVerifyState {
    pub builtin_recursive_goal_count: u8,
}

impl BuiltinRuleVerifyState {
    pub fn new() -> Self {
        Self {
            builtin_recursive_goal_count: 0,
        }
    }

    pub fn try_enter_recursive_goal(&mut self) -> bool {
        if self.builtin_recursive_goal_count >= 64 {
            return false;
        }
        self.builtin_recursive_goal_count += 1;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursive_goal_budget_allows_the_sixty_fourth_child_and_rejects_the_sixty_fifth() {
        let mut state = BuiltinRuleVerifyState::new();
        for expected_count in 1..=64 {
            assert!(state.try_enter_recursive_goal());
            assert_eq!(state.builtin_recursive_goal_count, expected_count);
        }
        assert!(!state.try_enter_recursive_goal());
        assert_eq!(state.builtin_recursive_goal_count, 64);
    }

    #[test]
    fn recursive_goal_budget_is_monotone_and_has_no_refund_operation() {
        let mut state = BuiltinRuleVerifyState::new();
        assert!(state.try_enter_recursive_goal());
        assert!(state.try_enter_recursive_goal());
        assert_eq!(state.builtin_recursive_goal_count, 2);
    }
}
