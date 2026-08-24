//! Tests for bounded builtin-rule recursion state.

use crate::verify::BuiltinRuleSearchState;

#[test]
fn builtin_rule_search_state_root_allows_one_rule() {
    let state = BuiltinRuleSearchState::initial();
    assert!(state.can_apply_rule());
}

#[test]
fn builtin_rule_search_state_child_blocks_another_rule() {
    let root = BuiltinRuleSearchState::initial();
    let child = root.after_applying_rule();
    assert!(!child.can_apply_rule());
    assert!(root.can_apply_rule());
}
