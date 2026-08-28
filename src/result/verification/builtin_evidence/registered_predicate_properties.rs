//! Registered reflexive, symmetric, and antisymmetric predicate evidence.

use crate::prelude::*;
use std::fmt;

/// Exact use of a previously proved and registered reflexivity theorem for a
/// user-defined binary predicate.
#[derive(Clone)]
pub struct RegisteredReflexivePredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
}

/// Exact use of a previously proved and registered permutation theorem for a
/// user-defined predicate. The enclosing builtin proof owns exactly one child
/// Result proving `expected_alternate`; `gather` records how the target's
/// arguments were reordered to obtain that premise.
#[derive(Clone)]
pub struct RegisteredSymmetricPredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
    pub gather: Vec<usize>,
    pub expected_alternate: Fact,
}

/// Exact use of a previously proved and registered antisymmetry theorem for a
/// user-defined binary predicate. The enclosing builtin proof owns the two
/// ordered predicate-premise child Results.
#[derive(Clone)]
pub struct RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub predicate_name: String,
}

impl RegisteredReflexivePredicateBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, predicate_name: String) -> Self {
        Self {
            expected_target,
            predicate_name,
        }
    }
}

impl RegisteredSymmetricPredicateBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        predicate_name: String,
        gather: Vec<usize>,
        expected_alternate: Fact,
    ) -> Self {
        Self {
            expected_target,
            predicate_name,
            gather,
            expected_alternate,
        }
    }
}

impl RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, predicate_name: String) -> Self {
        Self {
            expected_target,
            predicate_name,
        }
    }
}

impl fmt::Debug for RegisteredReflexivePredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredReflexivePredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .finish()
    }
}

impl fmt::Debug for RegisteredSymmetricPredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredSymmetricPredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .field("gather", &self.gather)
            .field("expected_alternate", &self.expected_alternate.to_string())
            .finish()
    }
}

impl fmt::Debug for RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("RegisteredAntisymmetricPredicateBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("predicate_name", &self.predicate_name)
            .finish()
    }
}
