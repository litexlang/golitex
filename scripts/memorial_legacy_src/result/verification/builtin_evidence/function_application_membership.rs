//! Function-application return-membership evidence.

use crate::prelude::*;
use std::fmt;

/// Exact dependent-elimination certificate for membership of a checked
/// function application in its instantiated defined return set. The sole
/// child proves that the application head belongs to the function space frozen
/// in `expected_head_membership`.
#[derive(Clone)]
pub struct FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub typed_return_set: Obj,
    pub expected_target: Fact,
    pub expected_head_membership: Fact,
}

impl FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    pub fn new(
        typed_return_set: Obj,
        expected_target: Fact,
        expected_head_membership: Fact,
    ) -> Self {
        Self {
            typed_return_set,
            expected_target,
            expected_head_membership,
        }
    }
}

impl fmt::Debug for FunctionApplicationReturnMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionApplicationReturnMembershipBuiltinRuleEvidence")
            .field("typed_return_set", &self.typed_return_set.to_string())
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_head_membership",
                &self.expected_head_membership.to_string(),
            )
            .finish()
    }
}
