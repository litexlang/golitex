use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonzeroExpressionOrientationToLeanIR {
    ExpressionOnLeft,
    ExpressionOnRight,
}

#[derive(Clone)]
pub struct DivNotEqualZeroToLeanIR {
    pub numerator: Obj,
    pub denominator: Obj,
    pub orientation: NonzeroExpressionOrientationToLeanIR,
}

impl DivNotEqualZeroToLeanIR {
    pub fn new(
        numerator: Obj,
        denominator: Obj,
        orientation: NonzeroExpressionOrientationToLeanIR,
    ) -> Self {
        Self {
            numerator,
            denominator,
            orientation,
        }
    }
}

impl fmt::Debug for DivNotEqualZeroToLeanIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("DivNotEqualZeroToLeanIR")
            .field("numerator", &self.numerator.to_string())
            .field("denominator", &self.denominator.to_string())
            .field("orientation", &self.orientation)
            .finish()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithmeticBuiltinRuleToLeanIR {
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
pub enum SetRelationDualityBuiltinRuleToLeanIR {
    SubsetFromSuperset,
    SupersetFromSubset,
    NotSubsetFromNotSuperset,
    NotSupersetFromNotSubset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetBuiltinRuleToLeanIR {
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
pub enum AbsoluteValueBuiltinRuleToLeanIR {
    NonnegativeIdentity,
    NonpositiveNegation,
    Product,
    PositiveFromNonzero,
}

#[derive(Clone)]
pub enum BuiltinRuleToLeanIR {
    DivNotEqualZero(DivNotEqualZeroToLeanIR),
    Arithmetic(ArithmeticBuiltinRuleToLeanIR),
    /// Not-equality is symmetric. Example: `a != b` proves `b != a`.
    NotEqualSymmetry,
    /// Subset and superset are the same containment with reversed arguments.
    /// Example: `A $subset B` proves `B $superset A`.
    SetRelationDuality(SetRelationDualityBuiltinRuleToLeanIR),
    Set(SetBuiltinRuleToLeanIR),
    AbsoluteValue(AbsoluteValueBuiltinRuleToLeanIR),
    /// Closed `$prime(n)` and `not $prime(n)` facts checked by u64 reflection.
    PrimeU64Reflection,
    /// Positive-real membership entails strict positivity.
    /// Example: `a $in R+` proves `0 < a`.
    PositiveRealMembership,
}

impl From<&BuiltinRuleEvidence> for BuiltinRuleToLeanIR {
    fn from(evidence: &BuiltinRuleEvidence) -> Self {
        match evidence {
            BuiltinRuleEvidence::DivNotEqualZero(evidence) => {
                let orientation = match evidence.orientation {
                    NonzeroExpressionOrientation::ExpressionOnLeft => {
                        NonzeroExpressionOrientationToLeanIR::ExpressionOnLeft
                    }
                    NonzeroExpressionOrientation::ExpressionOnRight => {
                        NonzeroExpressionOrientationToLeanIR::ExpressionOnRight
                    }
                };
                BuiltinRuleToLeanIR::DivNotEqualZero(DivNotEqualZeroToLeanIR::new(
                    evidence.numerator.clone(),
                    evidence.denominator.clone(),
                    orientation,
                ))
            }
            BuiltinRuleEvidence::Arithmetic(rule) => BuiltinRuleToLeanIR::Arithmetic(match rule {
                ArithmeticBuiltinRule::LessEqualFromStrictOrder => {
                    ArithmeticBuiltinRuleToLeanIR::LessEqualFromStrictOrder
                }
                ArithmeticBuiltinRule::GreaterEqualFromStrictOrder => {
                    ArithmeticBuiltinRuleToLeanIR::GreaterEqualFromStrictOrder
                }
                ArithmeticBuiltinRule::SubNonnegativeFromLessEqual => {
                    ArithmeticBuiltinRuleToLeanIR::SubNonnegativeFromLessEqual
                }
                ArithmeticBuiltinRule::SubPositiveFromLess => {
                    ArithmeticBuiltinRuleToLeanIR::SubPositiveFromLess
                }
                ArithmeticBuiltinRule::AddNonnegative => {
                    ArithmeticBuiltinRuleToLeanIR::AddNonnegative
                }
                ArithmeticBuiltinRule::AddPositive => ArithmeticBuiltinRuleToLeanIR::AddPositive,
                ArithmeticBuiltinRule::AddPositiveLeftStrict => {
                    ArithmeticBuiltinRuleToLeanIR::AddPositiveLeftStrict
                }
                ArithmeticBuiltinRule::AddPositiveRightStrict => {
                    ArithmeticBuiltinRuleToLeanIR::AddPositiveRightStrict
                }
                ArithmeticBuiltinRule::MulNonnegative => {
                    ArithmeticBuiltinRuleToLeanIR::MulNonnegative
                }
                ArithmeticBuiltinRule::MulPositive => ArithmeticBuiltinRuleToLeanIR::MulPositive,
                ArithmeticBuiltinRule::DivNonnegative => {
                    ArithmeticBuiltinRuleToLeanIR::DivNonnegative
                }
                ArithmeticBuiltinRule::DivPositive => ArithmeticBuiltinRuleToLeanIR::DivPositive,
                ArithmeticBuiltinRule::AddCommonLeftLessEqual => {
                    ArithmeticBuiltinRuleToLeanIR::AddCommonLeftLessEqual
                }
                ArithmeticBuiltinRule::SubRightNonnegativeLessEqual => {
                    ArithmeticBuiltinRuleToLeanIR::SubRightNonnegativeLessEqual
                }
                ArithmeticBuiltinRule::AddRightNonnegativeLessEqual => {
                    ArithmeticBuiltinRuleToLeanIR::AddRightNonnegativeLessEqual
                }
                ArithmeticBuiltinRule::AddComponentwiseLessEqual => {
                    ArithmeticBuiltinRuleToLeanIR::AddComponentwiseLessEqual
                }
                ArithmeticBuiltinRule::AddCommonLeftLess => {
                    ArithmeticBuiltinRuleToLeanIR::AddCommonLeftLess
                }
                ArithmeticBuiltinRule::AddComponentwiseLess => {
                    ArithmeticBuiltinRuleToLeanIR::AddComponentwiseLess
                }
                ArithmeticBuiltinRule::AddComponentwiseLessLessEqual => {
                    ArithmeticBuiltinRuleToLeanIR::AddComponentwiseLessLessEqual
                }
                ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => {
                    ArithmeticBuiltinRuleToLeanIR::AddComponentwiseLessEqualLess
                }
            }),
            BuiltinRuleEvidence::NotEqualSymmetry => BuiltinRuleToLeanIR::NotEqualSymmetry,
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                BuiltinRuleToLeanIR::SetRelationDuality(match rule {
                    SetRelationDualityBuiltinRule::SubsetFromSuperset => {
                        SetRelationDualityBuiltinRuleToLeanIR::SubsetFromSuperset
                    }
                    SetRelationDualityBuiltinRule::SupersetFromSubset => {
                        SetRelationDualityBuiltinRuleToLeanIR::SupersetFromSubset
                    }
                    SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset => {
                        SetRelationDualityBuiltinRuleToLeanIR::NotSubsetFromNotSuperset
                    }
                    SetRelationDualityBuiltinRule::NotSupersetFromNotSubset => {
                        SetRelationDualityBuiltinRuleToLeanIR::NotSupersetFromNotSubset
                    }
                })
            }
            BuiltinRuleEvidence::Set(rule) => BuiltinRuleToLeanIR::Set(match rule {
                SetBuiltinRule::UnionCommutative => SetBuiltinRuleToLeanIR::UnionCommutative,
                SetBuiltinRule::UnionAssociative => SetBuiltinRuleToLeanIR::UnionAssociative,
                SetBuiltinRule::UnionIdempotent => SetBuiltinRuleToLeanIR::UnionIdempotent,
                SetBuiltinRule::UnionEmptyIdentity => SetBuiltinRuleToLeanIR::UnionEmptyIdentity,
                SetBuiltinRule::IntersectCommutative => SetBuiltinRuleToLeanIR::IntersectCommutative,
                SetBuiltinRule::IntersectAssociative => SetBuiltinRuleToLeanIR::IntersectAssociative,
                SetBuiltinRule::UnionMembershipLeft => SetBuiltinRuleToLeanIR::UnionMembershipLeft,
                SetBuiltinRule::UnionMembershipRight => SetBuiltinRuleToLeanIR::UnionMembershipRight,
                SetBuiltinRule::IntersectMembershipBoth => SetBuiltinRuleToLeanIR::IntersectMembershipBoth,
                SetBuiltinRule::IntersectNonMembershipLeft => SetBuiltinRuleToLeanIR::IntersectNonMembershipLeft,
                SetBuiltinRule::IntersectNonMembershipRight => SetBuiltinRuleToLeanIR::IntersectNonMembershipRight,
                SetBuiltinRule::SetMinusMembership => SetBuiltinRuleToLeanIR::SetMinusMembership,
            }),
            BuiltinRuleEvidence::AbsoluteValue(rule) => BuiltinRuleToLeanIR::AbsoluteValue(match rule {
                AbsoluteValueBuiltinRule::NonnegativeIdentity => AbsoluteValueBuiltinRuleToLeanIR::NonnegativeIdentity,
                AbsoluteValueBuiltinRule::NonpositiveNegation => AbsoluteValueBuiltinRuleToLeanIR::NonpositiveNegation,
                AbsoluteValueBuiltinRule::Product => AbsoluteValueBuiltinRuleToLeanIR::Product,
                AbsoluteValueBuiltinRule::PositiveFromNonzero => AbsoluteValueBuiltinRuleToLeanIR::PositiveFromNonzero,
            }),
            BuiltinRuleEvidence::PrimeU64Reflection => BuiltinRuleToLeanIR::PrimeU64Reflection,
        }
    }
}

impl fmt::Debug for BuiltinRuleToLeanIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            BuiltinRuleToLeanIR::DivNotEqualZero(evidence) => {
                f.debug_tuple("DivNotEqualZero").field(evidence).finish()
            }
            BuiltinRuleToLeanIR::Arithmetic(rule) => {
                f.debug_tuple("Arithmetic").field(rule).finish()
            }
            BuiltinRuleToLeanIR::NotEqualSymmetry => f.write_str("NotEqualSymmetry"),
            BuiltinRuleToLeanIR::SetRelationDuality(rule) => {
                f.debug_tuple("SetRelationDuality").field(rule).finish()
            }
            BuiltinRuleToLeanIR::Set(rule) => f.debug_tuple("Set").field(rule).finish(),
            BuiltinRuleToLeanIR::AbsoluteValue(rule) => {
                f.debug_tuple("AbsoluteValue").field(rule).finish()
            }
            BuiltinRuleToLeanIR::PrimeU64Reflection => f.write_str("PrimeU64Reflection"),
            BuiltinRuleToLeanIR::PositiveRealMembership => f.write_str("PositiveRealMembership"),
        }
    }
}
