//! Closed, refined, and negative numeric-membership evidence.

use crate::prelude::*;
use std::fmt;

/// Exact constructor certificate for a refined standard numeric set. Children
/// are ordered as the native base-carrier membership followed by the defining
/// sign/nonzero predicate. The numeric set is recovered from `expected_target`.
#[derive(Clone)]
pub struct RefinedNumericMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_premises: Vec<Fact>,
}

/// A closed numeric expression was recursively evaluated and the resulting
/// number was checked against one standard numeric set.  The source expression
/// remains part of `expected_target`; `evaluation` records how it reached the
/// normalized value used by the membership decision.
#[derive(Clone)]
pub struct ClosedNumericMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
    pub evaluation: SuccessEvaluateObjResult,
}

/// The negative counterpart of `ClosedNumericMembershipBuiltinRuleEvidence`.
#[derive(Clone)]
pub struct ClosedNumericNonmembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub target_set: StandardSet,
    pub evaluation: SuccessEvaluateObjResult,
}

impl ClosedNumericMembershipBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        target_set: StandardSet,
        evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            target_set,
            evaluation,
        }
    }
}

impl fmt::Debug for ClosedNumericMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set.to_string())
            .field("evaluation", &self.evaluation)
            .finish()
    }
}

impl ClosedNumericNonmembershipBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        target_set: StandardSet,
        evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            target_set,
            evaluation,
        }
    }
}

impl fmt::Debug for ClosedNumericNonmembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericNonmembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("target_set", &self.target_set.to_string())
            .field("evaluation", &self.evaluation)
            .finish()
    }
}

impl RefinedNumericMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for RefinedNumericMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RefinedNumericMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_premises",
                &self
                    .expected_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}
