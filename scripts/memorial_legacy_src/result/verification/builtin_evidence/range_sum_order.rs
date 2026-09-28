//! Pointwise-order evidence for integer-range sums.

use crate::prelude::*;
use std::fmt;

/// Exact monotonicity certificate for two inclusive integer-range sums. The
/// verifier retains the endpoint equalities followed by one binder-owning
/// pointwise `forall` Result. The compiler may support only a reviewed subset
/// of aggregate carriers, but it must never reconstruct the lost binder from
/// the target expression.
#[derive(Clone)]
pub struct IntegerRangeSumPointwiseOrderBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_start_equality: Fact,
    pub expected_end_equality: Fact,
    pub expected_pointwise: Fact,
}

impl IntegerRangeSumPointwiseOrderBuiltinRuleEvidence {
    pub fn new(
        expected_target: Fact,
        expected_start_equality: Fact,
        expected_end_equality: Fact,
        expected_pointwise: Fact,
    ) -> Self {
        Self {
            expected_target,
            expected_start_equality,
            expected_end_equality,
            expected_pointwise,
        }
    }
}

impl fmt::Debug for IntegerRangeSumPointwiseOrderBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("IntegerRangeSumPointwiseOrderBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field(
                "expected_start_equality",
                &self.expected_start_equality.to_string(),
            )
            .field(
                "expected_end_equality",
                &self.expected_end_equality.to_string(),
            )
            .field("expected_pointwise", &self.expected_pointwise.to_string())
            .finish()
    }
}
