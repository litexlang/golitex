//! Rational, complex, and integral polynomial normalization evidence.

use crate::prelude::*;
use std::fmt;

/// Zero-premise equality certificate for two closed numeric expressions. Both
/// recursive evaluation trees are retained so a backend never has to infer
/// the normal form from a diagnostic label.
#[derive(Clone)]
pub struct RationalNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub left_evaluation: SuccessEvaluateObjResult,
    pub right_evaluation: SuccessEvaluateObjResult,
}

/// Equality certificate selected after ordinary rational-expression
/// normalization. Every denominator or negative-power base used by
/// cancellation is retained as an exact nonzero premise.
#[derive(Clone)]
pub struct RationalAlgebraicNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_nonzero_premises: Vec<Fact>,
}

/// Equality certificate selected only after exact bounded polynomial/rational
/// normalization with the relation `i * i = -1`. Every denominator or
/// negative-power base needed by that normalization is retained as an exact
/// nonzero premise; an empty list records a genuinely zero-premise identity.
#[derive(Clone)]
pub struct ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_nonzero_premises: Vec<Fact>,
}

/// A zero-premise identity in the deliberately small integral-polynomial
/// fragment: atoms and integer literals closed under `+`, `-`, `*`, and
/// nonnegative literal powers. Both verifier and compiler independently
/// recheck the exact target against that fragment.
#[derive(Clone)]
pub struct IntegralPolynomialNormalizationBuiltinRuleEvidence {
    pub expected_target: Fact,
}

impl fmt::Debug for IntegralPolynomialNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("IntegralPolynomialNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

impl RationalNormalizationBuiltinRuleEvidence {
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

impl RationalAlgebraicNormalizationBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_nonzero_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_nonzero_premises,
        }
    }
}

impl ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_nonzero_premises: Vec<Fact>) -> Self {
        Self {
            expected_target,
            expected_nonzero_premises,
        }
    }
}

impl fmt::Debug for RationalNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RationalNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("left_evaluation", &self.left_evaluation)
            .field("right_evaluation", &self.right_evaluation)
            .finish()
    }
}

impl fmt::Debug for RationalAlgebraicNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RationalAlgebraicNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_nonzero_premises",
                &self
                    .expected_nonzero_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl fmt::Debug for ComplexAlgebraicNormalizationBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ComplexAlgebraicNormalizationBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_nonzero_premises",
                &self
                    .expected_nonzero_premises
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}
