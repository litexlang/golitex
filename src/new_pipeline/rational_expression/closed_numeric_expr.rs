//! Closed numeric expression view (not an AST change to `Obj`).
//!
//! # What is "closed numeric"?
//!
//! A **closed numeric** expression is a pure number-literal arithmetic tree:
//! - leaves are only decimal [`Number`] values (e.g. `2`, `2.5`);
//! - interior nodes are only [`Add`] / [`Sub`] / [`Mul`] / [`Div`] / [`Pow`].
//!
//! It has **no** free identifiers, function calls, `%` / `quot` / `abs` /
//! trig / set ops, or other `Obj` constructors.
//!
//! Examples that **are** closed: `2`, `2^3/7 + 10 * 2.5`.
//! Examples that are **not**: `a + 1`, `abs(1)`, `1 % 2`.
//!
//! # Why [`ClosedNumericExpr`]?
//!
//! `Obj` still owns the language surface. This enum is a **classified view**:
//! `try_from_obj` succeeds only after the closed-numeric check, so a value of
//! type `ClosedNumericExpr` already means "this tree is closed numeric".
//! Closed-numeric store / rewrite paths should take this type (or produce it
//! at the boundary) instead of re-testing `Obj` ad hoc.

use crate::new_pipeline::ast::obj::{Add, Div, Mul, Number, Obj, Pow, Sub};

/// Classified closed-numeric tree. See module docs for the definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosedNumericExpr {
    Number(Number),
    Add(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Sub(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Mul(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Div(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Pow {
        base: Box<ClosedNumericExpr>,
        exponent: Box<ClosedNumericExpr>,
    },
}

impl ClosedNumericExpr {
    // Succeeds only when `obj` is closed numeric; failure means "not closed".
    // Example: `2 + 3` → Some; `a + 1` → None.
    pub fn try_from_obj(obj: &Obj) -> Option<Self> {
        match obj {
            Obj::Number(n) => Some(ClosedNumericExpr::Number(n.clone())),
            Obj::Add(add) => Some(ClosedNumericExpr::Add(
                Box::new(Self::try_from_obj(&add.left)?),
                Box::new(Self::try_from_obj(&add.right)?),
            )),
            Obj::Sub(sub) => Some(ClosedNumericExpr::Sub(
                Box::new(Self::try_from_obj(&sub.left)?),
                Box::new(Self::try_from_obj(&sub.right)?),
            )),
            Obj::Mul(mul) => Some(ClosedNumericExpr::Mul(
                Box::new(Self::try_from_obj(&mul.left)?),
                Box::new(Self::try_from_obj(&mul.right)?),
            )),
            Obj::Div(div) => Some(ClosedNumericExpr::Div(
                Box::new(Self::try_from_obj(&div.left)?),
                Box::new(Self::try_from_obj(&div.right)?),
            )),
            Obj::Pow(pow) => Some(ClosedNumericExpr::Pow {
                base: Box::new(Self::try_from_obj(&pow.base)?),
                exponent: Box::new(Self::try_from_obj(&pow.exponent)?),
            }),
            _ => None,
        }
    }

    pub fn to_obj(&self) -> Obj {
        match self {
            ClosedNumericExpr::Number(n) => Obj::Number(n.clone()),
            ClosedNumericExpr::Add(left, right) => Obj::Add(Add {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            }),
            ClosedNumericExpr::Sub(left, right) => Obj::Sub(Sub {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            }),
            ClosedNumericExpr::Mul(left, right) => Obj::Mul(Mul {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            }),
            ClosedNumericExpr::Div(left, right) => Obj::Div(Div {
                left: Box::new(left.to_obj()),
                right: Box::new(right.to_obj()),
            }),
            ClosedNumericExpr::Pow { base, exponent } => Obj::Pow(Pow {
                base: Box::new(base.to_obj()),
                exponent: Box::new(exponent.to_obj()),
            }),
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
    use crate::new_pipeline::ast::obj::{Add, Div, Mul, Number, Obj, Pow};

    fn n(s: &str) -> Obj {
        Obj::Number(Number {
            normalized_value: s.to_string(),
        })
    }

    #[test]
    fn number_and_arithmetic_pow_are_closed() {
        assert!(is_closed_numeric_expr(&n("2")));

        // 2^3/7 + 10 * 2.5
        let pow = Obj::Pow(Pow {
            base: Box::new(n("2")),
            exponent: Box::new(n("3")),
        });
        let frac = Obj::Div(Div {
            left: Box::new(pow),
            right: Box::new(n("7")),
        });
        let product = Obj::Mul(Mul {
            left: Box::new(n("10")),
            right: Box::new(n("2.5")),
        });
        let sum = Obj::Add(Add {
            left: Box::new(frac),
            right: Box::new(product),
        });
        let view = ClosedNumericExpr::try_from_obj(&sum).expect("closed");
        assert_eq!(view.to_obj().ir(), sum.ir());
    }

    #[test]
    fn identifier_and_abs_are_not_closed() {
        use crate::new_pipeline::ast::obj::{Abs, IdentifierObj};
        use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

        let ident = Obj::Identifier(IdentifierObj::plain(IdentifierId::new(0), "a".into()));
        assert!(ClosedNumericExpr::try_from_obj(&ident).is_none());

        let abs = Obj::Abs(Abs {
            arg: Box::new(n("1")),
        });
        assert!(ClosedNumericExpr::try_from_obj(&abs).is_none());
    }
}
