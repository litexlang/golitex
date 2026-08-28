//! Known-equality proof-chain evidence.

use crate::prelude::*;
use std::fmt;

/// Exact direct-equality path selected while checking one equality-class
/// result. Every step cites the environment-stored fact that justified it.
#[derive(Clone)]
pub struct KnownEqualityBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub steps: Vec<KnownEqualityBuiltinRuleStep>,
}

impl KnownEqualityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, steps: Vec<KnownEqualityBuiltinRuleStep>) -> Self {
        Self {
            expected_target,
            steps,
        }
    }
}

impl fmt::Debug for KnownEqualityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("KnownEqualityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("steps", &self.steps)
            .finish()
    }
}

#[derive(Clone)]
pub struct KnownEqualityBuiltinRuleStep {
    pub from: Obj,
    pub to: Obj,
    pub equality: EqualFact,
    pub source_fact_id: FactId,
}

impl KnownEqualityBuiltinRuleStep {
    pub fn new(from: Obj, to: Obj, equality: EqualFact, source_fact_id: FactId) -> Self {
        Self {
            from,
            to,
            equality,
            source_fact_id,
        }
    }
}

impl fmt::Debug for KnownEqualityBuiltinRuleStep {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("KnownEqualityBuiltinRuleStep")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("equality", &self.equality.to_string())
            .field("source_fact_id", &self.source_fact_id)
            .finish()
    }
}
