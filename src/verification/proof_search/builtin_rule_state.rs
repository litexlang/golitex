//! Recursion state for bounded builtin-rule proof search.

use crate::verification::VerifyState;

#[derive(Clone)]
pub struct BuiltinRuleSearchState {
    builtin_rule_depth: u8,
    verify_state: VerifyState,
}

impl BuiltinRuleSearchState {
    pub fn initial() -> Self {
        Self {
            builtin_rule_depth: 0,
            verify_state: VerifyState::initial(),
        }
    }

    pub(in crate::verification) fn in_proof_search(verify_state: &VerifyState) -> Self {
        Self {
            builtin_rule_depth: 0,
            verify_state: verify_state.clone(),
        }
    }

    pub fn can_apply_rule(&self) -> bool {
        self.builtin_rule_depth == 0
    }

    pub fn after_applying_rule(&self) -> Self {
        Self {
            builtin_rule_depth: self.builtin_rule_depth + 1,
            verify_state: self.verify_state.clone(),
        }
    }

    pub(in crate::verification) fn with_verify_state(&self, verify_state: &VerifyState) -> Self {
        Self {
            builtin_rule_depth: self.builtin_rule_depth,
            verify_state: verify_state.clone(),
        }
    }

    pub(in crate::verification) fn verify_state(&self) -> &VerifyState {
        &self.verify_state
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/verification/proof_search/builtin_rule_state.rs"]
mod tests;
