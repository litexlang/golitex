use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanNonzeroExpressionOrientationIr {
    ExpressionOnLeft,
    ExpressionOnRight,
}

#[derive(Clone)]
pub struct LitexToLeanDivNotEqualZeroIr {
    pub numerator: Obj,
    pub denominator: Obj,
    pub orientation: LitexToLeanNonzeroExpressionOrientationIr,
}

impl LitexToLeanDivNotEqualZeroIr {
    pub fn new(
        numerator: Obj,
        denominator: Obj,
        orientation: LitexToLeanNonzeroExpressionOrientationIr,
    ) -> Self {
        Self {
            numerator,
            denominator,
            orientation,
        }
    }
}

impl fmt::Debug for LitexToLeanDivNotEqualZeroIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("LitexToLeanDivNotEqualZeroIr")
            .field("numerator", &self.numerator.to_string())
            .field("denominator", &self.denominator.to_string())
            .field("orientation", &self.orientation)
            .finish()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanArithmeticBuiltinRuleIr {
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
pub enum LitexToLeanIntegerMembershipClosureBuiltinRuleIr {
    Add,
    Sub,
    Mul,
    Mod,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanSetRelationDualityBuiltinRuleIr {
    SubsetFromSuperset,
    SupersetFromSubset,
    NotSubsetFromNotSuperset,
    NotSupersetFromNotSubset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanSetBuiltinRuleIr {
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
pub enum LitexToLeanAbsoluteValueBuiltinRuleIr {
    NonnegativeIdentity,
    NonpositiveNegation,
    Product,
    PositiveFromNonzero,
}

#[derive(Clone)]
pub enum LitexToLeanBuiltinRuleIr {
    DivNotEqualZero(LitexToLeanDivNotEqualZeroIr),
    Arithmetic(LitexToLeanArithmeticBuiltinRuleIr),
    IntegerMembershipClosure(LitexToLeanIntegerMembershipClosureBuiltinRuleIr),
    /// Not-equality is symmetric. Example: `a != b` proves `b != a`.
    NotEqualSymmetry,
    /// A strict order between two checked real objects proves they differ.
    NotEqualFromStrictOrder,
    /// Subset and superset are the same containment with reversed arguments.
    /// Example: `A $subset B` proves `B $superset A`.
    SetRelationDuality(LitexToLeanSetRelationDualityBuiltinRuleIr),
    Set(LitexToLeanSetBuiltinRuleIr),
    AbsoluteValue(LitexToLeanAbsoluteValueBuiltinRuleIr),
    /// Closed `$prime(n)` and `not $prime(n)` facts checked by u64 reflection.
    PrimeU64Reflection,
    /// Membership in a standard numeric set is projected through Litex's
    /// centralized standard-set hierarchy. The proof has exactly one source
    /// membership premise.
    StandardSetMembershipProjection,
    /// Positive-real membership entails strict positivity.
    /// Example: `a $in R+` proves `0 < a`.
    PositiveRealMembership,
}

impl LitexToLeanBuiltinRuleIr {
    pub(crate) fn from_legacy_evidence(evidence: &BuiltinRuleEvidence) -> Option<Self> {
        Some(match evidence {
            BuiltinRuleEvidence::RegisteredLocal(_)
            | BuiltinRuleEvidence::DefinitionProjection(_)
            | BuiltinRuleEvidence::SetBuilderMembership(_)
            | BuiltinRuleEvidence::FunctionSetMembership(_)
            | BuiltinRuleEvidence::RefinedNumericMembership(_)
            | BuiltinRuleEvidence::ClosedNumericComparison(_)
            | BuiltinRuleEvidence::FunctionApplicationReturnMembership(_) => return None,
            BuiltinRuleEvidence::DivNotEqualZero(evidence) => {
                let orientation = match evidence.orientation {
                    NonzeroExpressionOrientation::ExpressionOnLeft => {
                        LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnLeft
                    }
                    NonzeroExpressionOrientation::ExpressionOnRight => {
                        LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnRight
                    }
                };
                LitexToLeanBuiltinRuleIr::DivNotEqualZero(LitexToLeanDivNotEqualZeroIr::new(
                    evidence.numerator.clone(),
                    evidence.denominator.clone(),
                    orientation,
                ))
            }
            BuiltinRuleEvidence::Arithmetic(rule) => {
                LitexToLeanBuiltinRuleIr::Arithmetic(match rule {
                    ArithmeticBuiltinRule::LessEqualFromStrictOrder => {
                        LitexToLeanArithmeticBuiltinRuleIr::LessEqualFromStrictOrder
                    }
                    ArithmeticBuiltinRule::GreaterEqualFromStrictOrder => {
                        LitexToLeanArithmeticBuiltinRuleIr::GreaterEqualFromStrictOrder
                    }
                    ArithmeticBuiltinRule::SubNonnegativeFromLessEqual => {
                        LitexToLeanArithmeticBuiltinRuleIr::SubNonnegativeFromLessEqual
                    }
                    ArithmeticBuiltinRule::SubPositiveFromLess => {
                        LitexToLeanArithmeticBuiltinRuleIr::SubPositiveFromLess
                    }
                    ArithmeticBuiltinRule::AddNonnegative => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddNonnegative
                    }
                    ArithmeticBuiltinRule::AddPositive => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddPositive
                    }
                    ArithmeticBuiltinRule::AddPositiveLeftStrict => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddPositiveLeftStrict
                    }
                    ArithmeticBuiltinRule::AddPositiveRightStrict => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddPositiveRightStrict
                    }
                    ArithmeticBuiltinRule::MulNonnegative => {
                        LitexToLeanArithmeticBuiltinRuleIr::MulNonnegative
                    }
                    ArithmeticBuiltinRule::MulPositive => {
                        LitexToLeanArithmeticBuiltinRuleIr::MulPositive
                    }
                    ArithmeticBuiltinRule::DivNonnegative => {
                        LitexToLeanArithmeticBuiltinRuleIr::DivNonnegative
                    }
                    ArithmeticBuiltinRule::DivPositive => {
                        LitexToLeanArithmeticBuiltinRuleIr::DivPositive
                    }
                    ArithmeticBuiltinRule::AddCommonLeftLessEqual => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddCommonLeftLessEqual
                    }
                    ArithmeticBuiltinRule::SubRightNonnegativeLessEqual => {
                        LitexToLeanArithmeticBuiltinRuleIr::SubRightNonnegativeLessEqual
                    }
                    ArithmeticBuiltinRule::AddRightNonnegativeLessEqual => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddRightNonnegativeLessEqual
                    }
                    ArithmeticBuiltinRule::AddComponentwiseLessEqual => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddComponentwiseLessEqual
                    }
                    ArithmeticBuiltinRule::AddCommonLeftLess => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddCommonLeftLess
                    }
                    ArithmeticBuiltinRule::AddComponentwiseLess => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddComponentwiseLess
                    }
                    ArithmeticBuiltinRule::AddComponentwiseLessLessEqual => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddComponentwiseLessLessEqual
                    }
                    ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => {
                        LitexToLeanArithmeticBuiltinRuleIr::AddComponentwiseLessEqualLess
                    }
                })
            }
            BuiltinRuleEvidence::IntegerMembershipClosure(rule) => {
                LitexToLeanBuiltinRuleIr::IntegerMembershipClosure(match rule {
                    IntegerMembershipClosureBuiltinRule::Add => {
                        LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Add
                    }
                    IntegerMembershipClosureBuiltinRule::Sub => {
                        LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Sub
                    }
                    IntegerMembershipClosureBuiltinRule::Mul => {
                        LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Mul
                    }
                    IntegerMembershipClosureBuiltinRule::Mod => {
                        LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Mod
                    }
                })
            }
            BuiltinRuleEvidence::NotEqualSymmetry => LitexToLeanBuiltinRuleIr::NotEqualSymmetry,
            BuiltinRuleEvidence::NotEqualFromStrictOrder => {
                LitexToLeanBuiltinRuleIr::NotEqualFromStrictOrder
            }
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                LitexToLeanBuiltinRuleIr::SetRelationDuality(match rule {
                    SetRelationDualityBuiltinRule::SubsetFromSuperset => {
                        LitexToLeanSetRelationDualityBuiltinRuleIr::SubsetFromSuperset
                    }
                    SetRelationDualityBuiltinRule::SupersetFromSubset => {
                        LitexToLeanSetRelationDualityBuiltinRuleIr::SupersetFromSubset
                    }
                    SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset => {
                        LitexToLeanSetRelationDualityBuiltinRuleIr::NotSubsetFromNotSuperset
                    }
                    SetRelationDualityBuiltinRule::NotSupersetFromNotSubset => {
                        LitexToLeanSetRelationDualityBuiltinRuleIr::NotSupersetFromNotSubset
                    }
                })
            }
            BuiltinRuleEvidence::Set(rule) => LitexToLeanBuiltinRuleIr::Set(match rule {
                SetBuiltinRule::UnionCommutative => LitexToLeanSetBuiltinRuleIr::UnionCommutative,
                SetBuiltinRule::UnionAssociative => LitexToLeanSetBuiltinRuleIr::UnionAssociative,
                SetBuiltinRule::UnionIdempotent => LitexToLeanSetBuiltinRuleIr::UnionIdempotent,
                SetBuiltinRule::UnionEmptyIdentity => {
                    LitexToLeanSetBuiltinRuleIr::UnionEmptyIdentity
                }
                SetBuiltinRule::IntersectCommutative => {
                    LitexToLeanSetBuiltinRuleIr::IntersectCommutative
                }
                SetBuiltinRule::IntersectAssociative => {
                    LitexToLeanSetBuiltinRuleIr::IntersectAssociative
                }
                SetBuiltinRule::UnionMembershipLeft => {
                    LitexToLeanSetBuiltinRuleIr::UnionMembershipLeft
                }
                SetBuiltinRule::UnionMembershipRight => {
                    LitexToLeanSetBuiltinRuleIr::UnionMembershipRight
                }
                SetBuiltinRule::IntersectMembershipBoth => {
                    LitexToLeanSetBuiltinRuleIr::IntersectMembershipBoth
                }
                SetBuiltinRule::IntersectNonMembershipLeft => {
                    LitexToLeanSetBuiltinRuleIr::IntersectNonMembershipLeft
                }
                SetBuiltinRule::IntersectNonMembershipRight => {
                    LitexToLeanSetBuiltinRuleIr::IntersectNonMembershipRight
                }
                SetBuiltinRule::SetMinusMembership => {
                    LitexToLeanSetBuiltinRuleIr::SetMinusMembership
                }
            }),
            BuiltinRuleEvidence::AbsoluteValue(rule) => {
                LitexToLeanBuiltinRuleIr::AbsoluteValue(match rule {
                    AbsoluteValueBuiltinRule::NonnegativeIdentity => {
                        LitexToLeanAbsoluteValueBuiltinRuleIr::NonnegativeIdentity
                    }
                    AbsoluteValueBuiltinRule::NonpositiveNegation => {
                        LitexToLeanAbsoluteValueBuiltinRuleIr::NonpositiveNegation
                    }
                    AbsoluteValueBuiltinRule::Product => {
                        LitexToLeanAbsoluteValueBuiltinRuleIr::Product
                    }
                    AbsoluteValueBuiltinRule::PositiveFromNonzero => {
                        LitexToLeanAbsoluteValueBuiltinRuleIr::PositiveFromNonzero
                    }
                })
            }
            BuiltinRuleEvidence::PrimeU64Reflection => LitexToLeanBuiltinRuleIr::PrimeU64Reflection,
            BuiltinRuleEvidence::StandardSetMembershipProjection => {
                LitexToLeanBuiltinRuleIr::StandardSetMembershipProjection
            }
        })
    }
}

impl fmt::Debug for LitexToLeanBuiltinRuleIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            LitexToLeanBuiltinRuleIr::DivNotEqualZero(evidence) => {
                f.debug_tuple("DivNotEqualZero").field(evidence).finish()
            }
            LitexToLeanBuiltinRuleIr::Arithmetic(rule) => {
                f.debug_tuple("Arithmetic").field(rule).finish()
            }
            LitexToLeanBuiltinRuleIr::IntegerMembershipClosure(rule) => f
                .debug_tuple("IntegerMembershipClosure")
                .field(rule)
                .finish(),
            LitexToLeanBuiltinRuleIr::NotEqualSymmetry => f.write_str("NotEqualSymmetry"),
            LitexToLeanBuiltinRuleIr::NotEqualFromStrictOrder => {
                f.write_str("NotEqualFromStrictOrder")
            }
            LitexToLeanBuiltinRuleIr::SetRelationDuality(rule) => {
                f.debug_tuple("SetRelationDuality").field(rule).finish()
            }
            LitexToLeanBuiltinRuleIr::Set(rule) => f.debug_tuple("Set").field(rule).finish(),
            LitexToLeanBuiltinRuleIr::AbsoluteValue(rule) => {
                f.debug_tuple("AbsoluteValue").field(rule).finish()
            }
            LitexToLeanBuiltinRuleIr::PrimeU64Reflection => f.write_str("PrimeU64Reflection"),
            LitexToLeanBuiltinRuleIr::StandardSetMembershipProjection => {
                f.write_str("StandardSetMembershipProjection")
            }
            LitexToLeanBuiltinRuleIr::PositiveRealMembership => {
                f.write_str("PositiveRealMembership")
            }
        }
    }
}
