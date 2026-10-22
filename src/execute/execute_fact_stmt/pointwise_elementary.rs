//! The five elementary real laws used by explicit BTs and structural certificates.
#[cfg(test)]
#[path = "../../../tests/unit/execute/pointwise_analysis/elementary.rs"]
mod elementary_pointwise_tests;
use super::helper::multiply_derivative_terms;
use crate::prelude::*;
use crate::rational_expression::helper::div_objs;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ElementaryRealFunction {
    Exp,
    Ln,
    Sin,
    Cos,
    Sqrt,
}

impl ElementaryRealFunction {
    pub fn from_expression(expression: &Obj) -> Option<(Self, &Obj)> {
        Some(match expression {
            Obj::ExpLogOperator(ExpLogOperator::Exp(v)) => (Self::Exp, &v.arg),
            Obj::ExpLogOperator(ExpLogOperator::Ln(v)) => (Self::Ln, &v.arg),
            Obj::TrigOperator(TrigOperator::Sin(v)) => (Self::Sin, &v.arg),
            Obj::TrigOperator(TrigOperator::Cos(v)) => (Self::Cos, &v.arg),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(v)) => (Self::Sqrt, &v.arg),
            _ => return None,
        })
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::Exp => "exp",
            Self::Ln => "ln",
            Self::Sin => "sin",
            Self::Cos => "cos",
            Self::Sqrt => "sqrt",
        }
    }
    pub fn apply(self, argument: Obj) -> Obj {
        match self {
            Self::Exp => Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
                arg: Box::new(argument),
            })),
            Self::Ln => Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
                arg: Box::new(argument),
            })),
            Self::Sin => Obj::TrigOperator(TrigOperator::Sin(Sin {
                arg: Box::new(argument),
            })),
            Self::Cos => Obj::TrigOperator(TrigOperator::Cos(Cos {
                arg: Box::new(argument),
            })),
            Self::Sqrt => Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
                arg: Box::new(argument),
            })),
        }
    }
    pub fn derivative_factor(self, argument: Obj) -> Obj {
        let number = |v: &str| Obj::Literal(Literal::Number(Number::new(v.into())));
        match self {
            Self::Exp => self.apply(argument),
            Self::Ln => div_objs(number("1"), argument),
            Self::Sin => Self::Cos.apply(argument),
            Self::Cos => Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
                arg: Box::new(Self::Sin.apply(argument)),
            })),
            // Sequential division keeps the original nonzero square-root obligation.
            Self::Sqrt => div_objs(div_objs(number("1"), number("2")), self.apply(argument)),
        }
    }
    pub fn derivative(self, argument: Obj, slope: Obj) -> Obj {
        // Standard chain formulas, with no redundant unit multiplier on a
        // primitive's identity argument. These are candidate construction,
        // not permission to search more broadly for an equality afterwards.
        match self {
            Self::Ln => div_objs(slope, argument),
            Self::Sqrt => div_objs(
                div_objs(
                    slope,
                    Obj::Literal(Literal::Number(Number::new("2".into()))),
                ),
                self.apply(argument),
            ),
            _ => {
                let factor = self.derivative_factor(argument);
                multiply_derivative_terms(factor, slope)
            }
        }
    }
}
impl Runtime {
    pub(crate) fn elementary_real_condition(
        &mut self,
        kind: ElementaryRealFunction,
        value: Obj,
        derivative: bool,
    ) -> Fact {
        if kind == ElementaryRealFunction::Sqrt && !derivative {
            LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::Literal(Literal::Number(Number::new("0".into()))),
                right: value,
                line_file: None,
            }
            .into()
        } else {
            let positive = matches!(kind, ElementaryRealFunction::Ln)
                || (kind == ElementaryRealFunction::Sqrt && derivative);
            InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: value,
                set: Obj::StandardSet(if positive {
                    StandardSet::RPos
                } else {
                    StandardSet::R
                }),
                line_file: None,
            }
            .into()
        }
    }
}
