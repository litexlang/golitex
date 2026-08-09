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

#[derive(Clone)]
pub enum BuiltinRuleToLeanIR {
    DivNotEqualZero(DivNotEqualZeroToLeanIR),
    Arithmetic(ArithmeticBuiltinRuleToLeanIR),
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
        }
    }
}
