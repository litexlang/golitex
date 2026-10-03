//! Syntax-directed extraction of an exact coefficient of pi.
use super::exact_rational::EvalRational;
use crate::ast::obj::{Add, ArithmeticOperator as A, Div, Literal, Mul, Neg, Obj, Sub};

pub(crate) fn pi_coefficient(angle: &Obj) -> Option<Obj> {
    coefficient(angle, 0)
}

fn coefficient(angle: &Obj, depth: usize) -> Option<Obj> {
    if depth > 64 {
        return None;
    }
    if EvalRational::from_obj(angle).is_some_and(|n| n.is_zero()) {
        return Some(EvalRational::new(0, 1)?.to_obj());
    }
    match angle {
        Obj::Literal(Literal::Pi(_)) => Some(EvalRational::new(1, 1)?.to_obj()),
        Obj::ArithmeticOperator(A::Add(a)) => Some(Obj::ArithmeticOperator(A::Add(Add {
            left: Box::new(coefficient(&a.left, depth + 1)?),
            right: Box::new(coefficient(&a.right, depth + 1)?),
        }))),
        Obj::ArithmeticOperator(A::Sub(a)) => Some(Obj::ArithmeticOperator(A::Sub(Sub {
            left: Box::new(coefficient(&a.left, depth + 1)?),
            right: Box::new(coefficient(&a.right, depth + 1)?),
        }))),
        Obj::ArithmeticOperator(A::Neg(a)) => Some(Obj::ArithmeticOperator(A::Neg(Neg {
            arg: Box::new(coefficient(&a.arg, depth + 1)?),
        }))),
        Obj::ArithmeticOperator(A::Mul(a)) => {
            if let Some(left) = coefficient(&a.left, depth + 1) {
                Some(Obj::ArithmeticOperator(A::Mul(Mul {
                    left: Box::new(left),
                    right: a.right.clone(),
                })))
            } else {
                Some(Obj::ArithmeticOperator(A::Mul(Mul {
                    left: a.left.clone(),
                    right: Box::new(coefficient(&a.right, depth + 1)?),
                })))
            }
        }
        Obj::ArithmeticOperator(A::Div(a)) => Some(Obj::ArithmeticOperator(A::Div(Div {
            left: Box::new(coefficient(&a.left, depth + 1)?),
            right: a.right.clone(),
        }))),
        _ => None,
    }
}
