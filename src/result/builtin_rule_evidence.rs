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

/// Stable identities for arithmetic/order rules whose complete certificate is
/// the target fact plus the recursively checked ordered premise list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithmeticBuiltinRule {
    LessEqualFromStrictOrder,
    GreaterEqualFromStrictOrder,
    SubNonnegativeFromLessEqual,
    SubPositiveFromLess,
    AddNonnegative,
    AddPositive,
    AddPositiveLeftStrict,
    AddPositiveRightStrict,
    MulNonnegative,
    MulPositive,
    DivNonnegative,
    DivPositive,
    AddCommonLeftLessEqual,
    SubRightNonnegativeLessEqual,
    AddRightNonnegativeLessEqual,
    AddComponentwiseLessEqual,
    AddCommonLeftLess,
    AddComponentwiseLess,
    AddComponentwiseLessLessEqual,
    AddComponentwiseLessEqualLess,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetRelationDualityBuiltinRule {
    SubsetFromSuperset,
    SupersetFromSubset,
    NotSubsetFromNotSuperset,
    NotSupersetFromNotSubset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetBuiltinRule {
    UnionCommutative,
    UnionAssociative,
    UnionIdempotent,
    UnionEmptyIdentity,
    IntersectCommutative,
    IntersectAssociative,
    UnionMembershipLeft,
    UnionMembershipRight,
    IntersectMembershipBoth,
    IntersectNonMembershipLeft,
    IntersectNonMembershipRight,
    SetMinusMembership,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbsoluteValueBuiltinRule {
    NonnegativeIdentity,
    NonpositiveNegation,
    Product,
    PositiveFromNonzero,
}

#[derive(Clone)]
pub enum BuiltinRuleEvidence {
    DivNotEqualZero(DivNotEqualZeroBuiltinRuleEvidence),
    Arithmetic(ArithmeticBuiltinRule),
    NotEqualSymmetry,
    SetRelationDuality(SetRelationDualityBuiltinRule),
    Set(SetBuiltinRule),
    AbsoluteValue(AbsoluteValueBuiltinRule),
    PrimeU64Reflection,
}

impl fmt::Debug for BuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BuiltinRuleEvidence::DivNotEqualZero(evidence) => {
                f.debug_tuple("DivNotEqualZero").field(evidence).finish()
            }
            BuiltinRuleEvidence::Arithmetic(rule) => {
                f.debug_tuple("Arithmetic").field(rule).finish()
            }
            BuiltinRuleEvidence::NotEqualSymmetry => f.write_str("NotEqualSymmetry"),
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                f.debug_tuple("SetRelationDuality").field(rule).finish()
            }
            BuiltinRuleEvidence::Set(rule) => f.debug_tuple("Set").field(rule).finish(),
            BuiltinRuleEvidence::AbsoluteValue(rule) => {
                f.debug_tuple("AbsoluteValue").field(rule).finish()
            }
            BuiltinRuleEvidence::PrimeU64Reflection => f.write_str("PrimeU64Reflection"),
        }
    }
}
