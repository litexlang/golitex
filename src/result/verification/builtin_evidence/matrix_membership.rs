//! Matrix-expression membership evidence.

use crate::prelude::*;
use std::fmt;

/// Exact carrier certificate for a native matrix expression. The enclosing
/// fact's recursive well-definedness result owns the operand carrier and
/// dimension checks; this payload records the matrix type computed by that
/// checked constructor and the membership proposition it discharges.
#[derive(Clone)]
pub struct MatrixExpressionMembershipBuiltinRuleEvidence {
    pub inferred_matrix_set: MatrixSet,
    pub expected_target: Fact,
}

impl fmt::Debug for MatrixExpressionMembershipBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("MatrixExpressionMembershipBuiltinRuleEvidence")
            .field(
                "inferred_matrix_set",
                &Obj::from(self.inferred_matrix_set.clone()).to_string(),
            )
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}
