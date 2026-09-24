//! Closed numeric expression view (not an AST change to Obj).
//!
//! A closed numeric expression is a pure number-literal arithmetic tree:
//! - leaves are only decimal Number values (e.g. `2`, `2.5`);
//! - interior nodes are the arithmetic operators that evaluate under
//!   evaluate_obj_to_normalized_decimal_number:
//!   `+ - * / pow abs min max floor ceil sign` and unary `-` (`neg`).
//!
//! It has no free identifiers, `%` / `quot` / gcd / trig / set ops, or
//! other Obj constructors.
//!
//! Examples that are closed: `2`, `2^3/7 + 10 * 2.5`, `abs(-3)`, `min(1, 2)`.
//! Examples that are not: `a + 1`, `1 % 2`, `sin(0)`.
//!
//! Obj still owns the language surface. This enum is a classified view:
//! try_from_obj succeeds only after the closed-numeric check, so a value of
//! type ClosedNumericExpr already means "this tree is closed numeric".
//! Closed-numeric store / rewrite paths should take this type (or produce it
//! at the boundary) instead of re-testing Obj ad hoc.

use crate::new_pipeline::ast::obj::{Abs, Add, Ceil, Div, Floor, Max, Min, Mul, Neg, Number, Obj, Pow, Sign, Sub, ArithmeticOperator, Literal};

/// Classified closed-numeric tree. See module docs for the definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosedNumericExpr {
    Number(Number),
    Add(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Sub(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Neg(Box<ClosedNumericExpr>),
    Mul(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Div(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Pow {
        base: Box<ClosedNumericExpr>,
        exponent: Box<ClosedNumericExpr>,
    },
    Abs(Box<ClosedNumericExpr>),
    Min(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Max(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Floor(Box<ClosedNumericExpr>),
    Ceil(Box<ClosedNumericExpr>),
    Sign(Box<ClosedNumericExpr>),
}

impl ClosedNumericExpr {
    // Succeeds only when `obj` is closed numeric; failure means "not closed".
    // Example: `2 + 3` → Some; `a + 1` → None; `abs(-3)` → Some.
    pub fn try_from_obj(obj: &Obj) -> Option<Self> {
        match obj {
            Obj::Literal(Literal::Number(n)) => Some(ClosedNumericExpr::Number(n.clone())),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) => Some(ClosedNumericExpr::Add(
                Box::new(Self::try_from_obj(&add.left)?),
                Box::new(Self::try_from_obj(&add.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) => Some(ClosedNumericExpr::Sub(
                Box::new(Self::try_from_obj(&sub.left)?),
                Box::new(Self::try_from_obj(&sub.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) => Some(ClosedNumericExpr::Neg(Box::new(Self::try_from_obj(
                &neg.arg,
            )?))),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) => Some(ClosedNumericExpr::Mul(
                Box::new(Self::try_from_obj(&mul.left)?),
                Box::new(Self::try_from_obj(&mul.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) => Some(ClosedNumericExpr::Div(
                Box::new(Self::try_from_obj(&div.left)?),
                Box::new(Self::try_from_obj(&div.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)) => Some(ClosedNumericExpr::Pow {
                base: Box::new(Self::try_from_obj(&pow.base)?),
                exponent: Box::new(Self::try_from_obj(&pow.exponent)?),
            }),
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) => Some(ClosedNumericExpr::Abs(Box::new(Self::try_from_obj(
                &abs.arg,
            )?))),
            Obj::ArithmeticOperator(ArithmeticOperator::Min(min)) => Some(ClosedNumericExpr::Min(
                Box::new(Self::try_from_obj(&min.left)?),
                Box::new(Self::try_from_obj(&min.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Max(max)) => Some(ClosedNumericExpr::Max(
                Box::new(Self::try_from_obj(&max.left)?),
                Box::new(Self::try_from_obj(&max.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(floor)) => Some(ClosedNumericExpr::Floor(Box::new(Self::try_from_obj(
                &floor.arg,
            )?))),
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(ceil)) => Some(ClosedNumericExpr::Ceil(Box::new(Self::try_from_obj(
                &ceil.arg,
            )?))),
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(sign)) => Some(ClosedNumericExpr::Sign(Box::new(Self::try_from_obj(
                &sign.arg,
            )?))),
            _ => None,
        }
    }

    pub fn to_obj(&self) -> Obj {
        match self {
            ClosedNumericExpr::Number(n) => Obj::Literal(Literal::Number(n.clone())),
            ClosedNumericExpr::Add(left, right) => Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            })),
            ClosedNumericExpr::Sub(left, right) => Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            })),
            ClosedNumericExpr::Neg(arg) => Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
                arg: Box::new(arg.to_obj()),
            })),
            ClosedNumericExpr::Mul(left, right) => Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            })),
            ClosedNumericExpr::Div(left, right) => Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            })),
            ClosedNumericExpr::Pow { base, exponent } => Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                base: Box::new(base.to_obj()),
                exponent: Box::new(exponent.to_obj()),
            })),
            ClosedNumericExpr::Abs(arg) => Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
                arg: Box::new(arg.to_obj()),
            })),
            ClosedNumericExpr::Min(left, right) => Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            })),
            ClosedNumericExpr::Max(left, right) => Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            })),
            ClosedNumericExpr::Floor(arg) => Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
                arg: Box::new(arg.to_obj()),
            })),
            ClosedNumericExpr::Ceil(arg) => Obj::ArithmeticOperator(ArithmeticOperator::Ceil(Ceil {
                arg: Box::new(arg.to_obj()),
            })),
            ClosedNumericExpr::Sign(arg) => Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
                arg: Box::new(arg.to_obj()),
            })),
        }
    }
}

// Predicate form of classification (same meaning as `try_from_obj(...).is_some()`).
pub fn is_closed_numeric_expr(obj: &Obj) -> bool {
    ClosedNumericExpr::try_from_obj(obj).is_some()
}

#[cfg(test)]
mod tests {
    use super::{is_closed_numeric_expr, ClosedNumericExpr};
    use crate::new_pipeline::ast::obj::{Abs, Add, Div, Floor, Max, Min, Mul, Number, Obj, Pow, Sign, ArithmeticOperator, Literal};

    fn n(s: &str) -> Obj {
        Obj::Literal(Literal::Number(Number {
            normalized_value: s.to_string(),
        }))
    }

    #[test]
    fn number_and_arithmetic_pow_are_closed() {
        assert!(is_closed_numeric_expr(&n("2")));

        // 2^3/7 + 10 * 2.5
        let pow = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(n("2")),
            exponent: Box::new(n("3")),
        }));
        let frac = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: Box::new(pow),
            right: Box::new(n("7")),
        }));
        let product = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(n("10")),
            right: Box::new(n("2.5")),
        }));
        let sum = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
            left: Box::new(frac),
            right: Box::new(product),
        }));
        let view = ClosedNumericExpr::try_from_obj(&sum).expect("closed");
        assert_eq!(view.to_obj().ir(), sum.ir());
    }

    #[test]
    fn abs_min_max_floor_sign_of_numbers_are_closed() {
        let abs = Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
            arg: Box::new(n("-3")),
        }));
        assert!(is_closed_numeric_expr(&abs));
        assert_eq!(
            ClosedNumericExpr::try_from_obj(&abs)
                .unwrap()
                .to_obj()
                .ir(),
            abs.ir()
        );

        let min = Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
            left: Box::new(n("1")),
            right: Box::new(n("2")),
        }));
        assert!(is_closed_numeric_expr(&min));

        let max = Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
            left: Box::new(n("1")),
            right: Box::new(n("2")),
        }));
        assert!(is_closed_numeric_expr(&max));

        let floor = Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
            arg: Box::new(n("2.5")),
        }));
        assert!(is_closed_numeric_expr(&floor));

        let sign = Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
            arg: Box::new(n("-2")),
        }));
        assert!(is_closed_numeric_expr(&sign));
    }

    #[test]
    fn unary_neg_of_number_is_closed() {
        use crate::new_pipeline::ast::obj::Neg;
        let neg = Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
            arg: Box::new(n("3")),
        }));
        assert!(is_closed_numeric_expr(&neg));
        assert_eq!(
            ClosedNumericExpr::try_from_obj(&neg)
                .unwrap()
                .to_obj()
                .ir(),
            neg.ir()
        );
    }

    #[test]
    fn identifier_is_not_closed() {
        use crate::new_pipeline::ast::obj::IdentifierObj;
        use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

        let ident = Obj::Identifier(IdentifierObj::plain(IdentifierId::new(0), "a".into()));
        assert!(ClosedNumericExpr::try_from_obj(&ident).is_none());
    }
}
