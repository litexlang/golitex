//! Nonzero evidence for division expressions.

use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonzeroExpressionOrientation {
    ExpressionOnLeft,
    ExpressionOnRight,
}

#[derive(Clone)]
pub struct DivNotEqualZeroBuiltinRuleEvidence {
    pub numerator: Obj,
    pub denominator: Obj,
    pub orientation: NonzeroExpressionOrientation,
}

impl DivNotEqualZeroBuiltinRuleEvidence {
    pub fn rule_id(&self) -> &'static str {
        "nonzero.div"
    }

    pub fn new(
        numerator: Obj,
        denominator: Obj,
        orientation: NonzeroExpressionOrientation,
    ) -> Self {
        Self {
            numerator,
            denominator,
            orientation,
        }
    }
}

impl fmt::Debug for DivNotEqualZeroBuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("DivNotEqualZeroBuiltinRuleEvidence")
            .field("numerator", &self.numerator.to_string())
            .field("denominator", &self.denominator.to_string())
            .field("orientation", &self.orientation)
            .finish()
    }
}
