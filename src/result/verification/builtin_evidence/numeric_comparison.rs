//! Closed and runtime-resolved numeric comparison evidence.

use crate::prelude::*;
use std::fmt;

/// A closed literal numeric comparison checked by the verifier's evaluator.
/// The Lean carrier remains contextual (for example `0 < 1` may be needed in
/// an `ℝ` proof), so the certificate freezes the proposition without choosing a
/// different source-level numeric set.
#[derive(Clone)]
pub struct ClosedNumericComparisonBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub left_evaluation: SuccessEvaluateObjResult,
    pub right_evaluation: SuccessEvaluateObjResult,
}

/// A weak order on one object, or the negation of a strict order on that same
/// object, discharged by reflexivity/irreflexivity rather than calculation.
///
/// Keeping this separate from `ClosedNumericComparisonBuiltinRuleEvidence`
/// matters for compositional consumers: `x <= x` is valid in a local binder
/// environment even though `x` is not a closed numeric expression.
#[derive(Clone)]
pub struct OrderReflexivityBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub repeated_object: Obj,
}

/// Compatibility evidence for a comparison decided only after `Runtime`
/// substituted known object values. The resolved operands are retained so the
/// execution Result says what was compared, but a standalone compiler must
/// reject this route until the substitutions themselves carry cited FactIds.
#[derive(Clone)]
pub struct RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub normalized_left: Obj,
    pub normalized_right: Obj,
}

impl ClosedNumericComparisonBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        left_evaluation: SuccessEvaluateObjResult,
        right_evaluation: SuccessEvaluateObjResult,
    ) -> Self {
        Self {
            expected_target,
            left_evaluation,
            right_evaluation,
        }
    }
}

impl OrderReflexivityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, repeated_object: Obj) -> Self {
        Self {
            expected_target,
            repeated_object,
        }
    }
}

impl RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, normalized_left: Obj, normalized_right: Obj) -> Self {
        Self {
            expected_target,
            normalized_left,
            normalized_right,
        }
    }
}

impl fmt::Debug for ClosedNumericComparisonBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ClosedNumericComparisonBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("left_evaluation", &self.left_evaluation)
            .field("right_evaluation", &self.right_evaluation)
            .finish()
    }
}

impl fmt::Debug for OrderReflexivityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("OrderReflexivityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("repeated_object", &self.repeated_object.to_string())
            .finish()
    }
}

impl fmt::Debug for RuntimeResolvedNumericComparisonBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RuntimeResolvedNumericComparisonBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("normalized_left", &self.normalized_left.to_string())
            .field("normalized_right", &self.normalized_right.to_string())
            .finish()
    }
}
