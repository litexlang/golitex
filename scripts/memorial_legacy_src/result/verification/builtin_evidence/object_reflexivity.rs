//! Object reflexivity evidence.

use crate::prelude::*;
use std::fmt;

/// Zero-premise equality certificate whose two source objects are exactly the
/// same object after parser-owned binding identity is taken into account.
#[derive(Clone)]
pub struct ObjectReflexivityBuiltinRuleEvidence {
    pub expected_target: Fact,
}

impl ObjectReflexivityBuiltinRuleEvidence {
    pub fn new(expected_target: Fact) -> Self {
        Self { expected_target }
    }
}

impl fmt::Debug for ObjectReflexivityBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("ObjectReflexivityBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}
