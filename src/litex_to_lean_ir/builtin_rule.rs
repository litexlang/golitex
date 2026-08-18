use crate::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanNonzeroExpressionOrientationIr {
    ExpressionOnLeft,
    ExpressionOnRight,
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
pub enum LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanNativeConstantMembershipBuiltinRuleIr {
    ImaginaryUnitInComplex,
    EulerNumberInReal,
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

/// Exact verifier-selected builtin evidence. Some variants are consumed as
/// parameter or WD certificates by an enclosing replay rule rather than
/// rendered as standalone Lean proof terms.
#[derive(Clone, Debug)]
pub enum LitexToLeanBuiltinRuleIr {
    DivNotEqualZero(LitexToLeanNonzeroExpressionOrientationIr),
    Arithmetic(LitexToLeanArithmeticBuiltinRuleIr),
    IntegerMembershipClosure(LitexToLeanIntegerMembershipClosureBuiltinRuleIr),
    ComplexArithmeticMembershipClosure(LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr),
    RealArithmeticMembershipClosure(LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr),
    NativeConstantMembership(LitexToLeanNativeConstantMembershipBuiltinRuleIr),
    NotEqualSymmetry,
    NotEqualFromStrictOrder,
    SetRelationDuality(LitexToLeanSetRelationDualityBuiltinRuleIr),
    Set(LitexToLeanSetBuiltinRuleIr),
    AbsoluteValue(LitexToLeanAbsoluteValueBuiltinRuleIr),
    PrimeU64Reflection,
    CoprimeNaturalReflection,
    StandardSetMembershipProjection,
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
            | BuiltinRuleEvidence::DisjunctionIntroduction(_)
            | BuiltinRuleEvidence::FunctionApplicationReturnMembership(_)
            | BuiltinRuleEvidence::KnownEqualityPath(_) => return None,
            BuiltinRuleEvidence::DivNotEqualZero(evidence) => {
                Self::DivNotEqualZero(match evidence.orientation {
                    NonzeroExpressionOrientation::ExpressionOnLeft => {
                        LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnLeft
                    }
                    NonzeroExpressionOrientation::ExpressionOnRight => {
                        LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnRight
                    }
                })
            }
            BuiltinRuleEvidence::Arithmetic(rule) => Self::Arithmetic(match rule {
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
            }),
            BuiltinRuleEvidence::IntegerMembershipClosure(rule) => {
                Self::IntegerMembershipClosure(match rule {
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
            BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule) => {
                Self::ComplexArithmeticMembershipClosure(match rule {
                    ComplexArithmeticMembershipClosureBuiltinRule::Add => {
                        LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Add
                    }
                    ComplexArithmeticMembershipClosureBuiltinRule::Sub => {
                        LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Sub
                    }
                    ComplexArithmeticMembershipClosureBuiltinRule::Mul => {
                        LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Mul
                    }
                    ComplexArithmeticMembershipClosureBuiltinRule::Div => {
                        LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Div
                    }
                })
            }
            BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule) => {
                Self::RealArithmeticMembershipClosure(match rule {
                    RealArithmeticMembershipClosureBuiltinRule::Add => {
                        LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Add
                    }
                    RealArithmeticMembershipClosureBuiltinRule::Sub => {
                        LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Sub
                    }
                    RealArithmeticMembershipClosureBuiltinRule::Mul => {
                        LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Mul
                    }
                    RealArithmeticMembershipClosureBuiltinRule::Div => {
                        LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div
                    }
                    RealArithmeticMembershipClosureBuiltinRule::Pow => {
                        LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Pow
                    }
                })
            }
            BuiltinRuleEvidence::NativeConstantMembership(rule) => {
                Self::NativeConstantMembership(match rule {
                    NativeConstantMembershipBuiltinRule::ImaginaryUnitInComplex => {
                        LitexToLeanNativeConstantMembershipBuiltinRuleIr::ImaginaryUnitInComplex
                    }
                    NativeConstantMembershipBuiltinRule::EulerNumberInReal => {
                        LitexToLeanNativeConstantMembershipBuiltinRuleIr::EulerNumberInReal
                    }
                })
            }
            BuiltinRuleEvidence::NotEqualSymmetry => Self::NotEqualSymmetry,
            BuiltinRuleEvidence::NotEqualFromStrictOrder => Self::NotEqualFromStrictOrder,
            BuiltinRuleEvidence::SetRelationDuality(rule) => Self::SetRelationDuality(match rule {
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
            }),
            BuiltinRuleEvidence::Set(rule) => Self::Set(match rule {
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
            BuiltinRuleEvidence::AbsoluteValue(rule) => Self::AbsoluteValue(match rule {
                AbsoluteValueBuiltinRule::NonnegativeIdentity => {
                    LitexToLeanAbsoluteValueBuiltinRuleIr::NonnegativeIdentity
                }
                AbsoluteValueBuiltinRule::NonpositiveNegation => {
                    LitexToLeanAbsoluteValueBuiltinRuleIr::NonpositiveNegation
                }
                AbsoluteValueBuiltinRule::Product => LitexToLeanAbsoluteValueBuiltinRuleIr::Product,
                AbsoluteValueBuiltinRule::PositiveFromNonzero => {
                    LitexToLeanAbsoluteValueBuiltinRuleIr::PositiveFromNonzero
                }
            }),
            BuiltinRuleEvidence::PrimeU64Reflection => Self::PrimeU64Reflection,
            BuiltinRuleEvidence::CoprimeNaturalReflection => Self::CoprimeNaturalReflection,
            BuiltinRuleEvidence::StandardSetMembershipProjection => {
                Self::StandardSetMembershipProjection
            }
        })
    }
}

pub(super) fn litex_to_lean_builtin_rule_from_verified_strategy_label(
    label: &str,
    goal: &Fact,
) -> Option<LitexToLeanBuiltinRuleIr> {
    if label != "numeric-carrier strategy: structural closure in R" {
        return None;
    }
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = goal else {
        return None;
    };
    if !matches!(membership.set, Obj::StandardSet(StandardSet::R)) {
        return None;
    }
    let rule = match &membership.element {
        Obj::Add(_) => LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Add,
        Obj::Sub(_) => LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Sub,
        Obj::Mul(_) => LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Mul,
        Obj::Div(_) => LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div,
        _ => return None,
    };
    Some(LitexToLeanBuiltinRuleIr::RealArithmeticMembershipClosure(
        rule,
    ))
}
