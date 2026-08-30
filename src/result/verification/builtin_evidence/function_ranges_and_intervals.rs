//! Function-range and real-interval builtin evidence.

use crate::prelude::*;
use std::fmt;

/// A finite interval or one-sided ray is contained in the exact real carrier.
/// The enclosing Result retains endpoint well-definedness separately; this
/// certificate freezes the proposition selected by the verifier.
#[derive(Clone)]
pub struct RealIntervalSubsetRealBuiltinRuleEvidence {
    pub expected_target: Fact,
}

/// One checked application of the same function that heads the retained
/// range introduces membership in that exact range.
#[derive(Clone)]
pub struct FunctionApplicationInRangeBuiltinRuleEvidence {
    pub expected_target: Fact,
}

/// A function range is included in any set containing its exact codomain.
/// The sole child Result must prove `expected_codomain_subset`.
#[derive(Clone)]
pub struct FunctionRangeSubsetBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_codomain_subset: Fact,
}

impl RealIntervalSubsetRealBuiltinRuleEvidence {
    pub fn new(expected_target: Fact) -> Self {
        Self { expected_target }
    }
}

impl FunctionApplicationInRangeBuiltinRuleEvidence {
    pub fn new(expected_target: Fact) -> Self {
        Self { expected_target }
    }
}

impl FunctionRangeSubsetBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_codomain_subset: Fact) -> Self {
        Self {
            expected_target,
            expected_codomain_subset,
        }
    }
}

impl fmt::Debug for RealIntervalSubsetRealBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RealIntervalSubsetRealBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

impl fmt::Debug for FunctionApplicationInRangeBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionApplicationInRangeBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}

impl fmt::Debug for FunctionRangeSubsetBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("FunctionRangeSubsetBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_codomain_subset",
                &self.expected_codomain_subset.to_string(),
            )
            .finish()
    }
}
