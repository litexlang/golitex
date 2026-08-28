//! Standard-set nonemptiness evidence.

use crate::prelude::*;
use std::fmt;

/// A standard carrier is inhabited by its reviewed canonical witness. The
/// target is retained explicitly so consumers never recover this rule from a
/// diagnostic label.
#[derive(Clone)]
pub struct StandardSetNonemptyBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
}

impl fmt::Debug for StandardSetNonemptyBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("StandardSetNonemptyBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set)
            .finish()
    }
}
