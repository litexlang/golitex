//! Set-builder, function-set, list-set, tuple, and Cartesian membership evidence.

use crate::prelude::*;
use std::fmt;

/// A checked equality with one exact source position introduces membership in
/// a finite list-set literal. The enclosing result retains that equality as
/// its sole child; the index fixes the coproduct injection path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListSetMembershipBuiltinRuleEvidence {
    pub selected_index: usize,
}

/// Exact constructor certificate for membership in a literal set builder.
/// Child results are ordered as base membership followed by the instantiated
/// defining facts in source order. The builder is recovered from
/// `expected_target`.
#[derive(Clone)]
pub struct SetBuilderMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_premises: Vec<Fact>,
}

/// Exact extensional certificate for membership in a Litex function space.
/// The enclosing result has exactly one child: the checked pointwise `forall`
/// proposition retained in `expected_pointwise`. The element and function
/// space are recovered from `expected_target`.
#[derive(Clone)]
pub struct FunctionSetMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_pointwise: Fact,
}

/// Exact constructor certificate for a literal tuple in a literal Cartesian
/// product. The verifier retains coordinate memberships in source order; for
/// arity greater than one they are checked by one conjunction child Result.
#[derive(Clone)]
pub struct TupleCartesianMembershipBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_coordinate_memberships: Vec<Fact>,
}

impl FunctionSetMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_pointwise: Fact) -> Self {
        Self {
            expected_target,
            expected_pointwise,
        }
    }
}

impl TupleCartesianMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_coordinate_memberships: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_coordinate_memberships,
        }
    }
}

impl fmt::Debug for TupleCartesianMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("TupleCartesianMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_coordinate_memberships",
                &self
                    .expected_coordinate_memberships
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl fmt::Debug for FunctionSetMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionSetMembershipBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("expected_pointwise", &self.expected_pointwise.to_string())
            .finish()
    }
}

impl SetBuilderMembershipBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_premises,
        }
    }
}

impl fmt::Debug for SetBuilderMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("SetBuilderMembershipBuiltinRuleEvidence")
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
