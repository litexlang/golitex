//! Closed numeric expression view (not an AST change to Obj).
//!
//! A closed numeric expression is a pure number-literal arithmetic tree:
//! - leaves are only decimal Number values (e.g. `2`, `2.5`);
//! - interior nodes are arithmetic / integer / detectable exp-log ops that
//!   evaluate under evaluate_obj_to_normalized_decimal_number when defined:
//!   `+ - * / pow abs min max floor ceil sign`,
//!   `% quot gcd lcm factorial` (integer-domain gate at classify time),
//!   `sqrt` / `log` (children closed; fold only when perfect square / integer power).
//!
//! It has no free identifiers, trig / set ops, or other Obj constructors.
//!
//! Simple closed examples: `2`, `2^3/7 + 10 * 2.5`, `abs(-3)`, `3!`,
//! `gcd(12, 8)`, `sqrt(4)`, `log(2, 8)`.
//! Complex nested closed examples (run these tracers):
//!   `examples/new_pipeline/proof_nodes/equal/by_builtin_rule/calculation_closed_decimal_complex_nested.lit`
//!   `examples/new_pipeline/stmt_nodes/command/eval_closed_numeric_complex.lit`
//! e.g. `sqrt(4) * log(2, 8) + floor(2.5)! = 8`,
//!      `((-7) % 3)^log(2, 4) + sqrt(0.36) = 4.6`.
//! Examples that are not closed: `a + 1`, `2.5 % 1`, `sin(0)`, `sqrt(2)` (fold fails).
//!
//! Obj still owns the language surface. This enum is a classified view:
//! try_from_obj succeeds only after the closed-numeric check, so a value of
//! type ClosedNumericExpr already means "this tree is closed numeric".
//! Actual numeric folding is not duplicated here: callers use the small shared
//! calculator `evaluate_obj_to_normalized_decimal_number` (equality, order,
//! membership, eval, and integer-domain gates). That single leaf is the
//! maintainable core of closed-numeric runtime behavior.
//! Closed-numeric store / rewrite paths should take this type (or produce it
//! at the boundary) instead of re-testing Obj ad hoc.

use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Ceil, Div, ExpLogOperator, Factorial, Floor, Gcd, IntegerOperator,
    Lcm, Literal, Log, Max, Min, Mod, Mul, Neg, Number, Obj, Pow, Quot, Sign, Sqrt, Sub,
};
use crate::rational_expression::decimal_arithmetic::{
    evaluate_obj_to_normalized_decimal_number, normalized_decimal_str_is_integer,
    normalized_decimal_str_is_non_negative_integer, normalize_decimal_number_string,
};

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
    Mod(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Quot(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Gcd(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Lcm(Box<ClosedNumericExpr>, Box<ClosedNumericExpr>),
    Factorial(Box<ClosedNumericExpr>),
    Sqrt(Box<ClosedNumericExpr>),
    Log {
        base: Box<ClosedNumericExpr>,
        arg: Box<ClosedNumericExpr>,
    },
}

impl ClosedNumericExpr {
    // Succeeds only when `obj` is closed numeric; failure means "not closed".
    // Example: `2 + 3` → Some; `a + 1` → None; `3!` → Some; `2.5 % 1` → None.
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
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) => Some(ClosedNumericExpr::Neg(
                Box::new(Self::try_from_obj(&neg.arg)?),
            )),
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
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) => Some(ClosedNumericExpr::Abs(
                Box::new(Self::try_from_obj(&abs.arg)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Min(min)) => Some(ClosedNumericExpr::Min(
                Box::new(Self::try_from_obj(&min.left)?),
                Box::new(Self::try_from_obj(&min.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Max(max)) => Some(ClosedNumericExpr::Max(
                Box::new(Self::try_from_obj(&max.left)?),
                Box::new(Self::try_from_obj(&max.right)?),
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(floor)) => {
                Some(ClosedNumericExpr::Floor(Box::new(Self::try_from_obj(
                    &floor.arg,
                )?)))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(ceil)) => {
                Some(ClosedNumericExpr::Ceil(Box::new(Self::try_from_obj(
                    &ceil.arg,
                )?)))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(sign)) => {
                Some(ClosedNumericExpr::Sign(Box::new(Self::try_from_obj(
                    &sign.arg,
                )?)))
            }
            Obj::IntegerOperator(IntegerOperator::Mod(mod_obj)) => {
                let left = Self::try_from_obj(&mod_obj.left)?;
                let right = Self::try_from_obj(&mod_obj.right)?;
                if !integer_mod_operands_ok(&left, &right) {
                    return None;
                }
                Some(ClosedNumericExpr::Mod(Box::new(left), Box::new(right)))
            }
            Obj::IntegerOperator(IntegerOperator::Quot(quot)) => {
                let left = Self::try_from_obj(&quot.left)?;
                let right = Self::try_from_obj(&quot.right)?;
                if !integer_quot_operands_ok(&left, &right) {
                    return None;
                }
                Some(ClosedNumericExpr::Quot(Box::new(left), Box::new(right)))
            }
            Obj::IntegerOperator(IntegerOperator::Gcd(gcd)) => {
                let left = Self::try_from_obj(&gcd.left)?;
                let right = Self::try_from_obj(&gcd.right)?;
                if !both_evaluate_to_integers(&left, &right) {
                    return None;
                }
                Some(ClosedNumericExpr::Gcd(Box::new(left), Box::new(right)))
            }
            Obj::IntegerOperator(IntegerOperator::Lcm(lcm)) => {
                let left = Self::try_from_obj(&lcm.left)?;
                let right = Self::try_from_obj(&lcm.right)?;
                if !both_evaluate_to_integers(&left, &right) {
                    return None;
                }
                Some(ClosedNumericExpr::Lcm(Box::new(left), Box::new(right)))
            }
            Obj::IntegerOperator(IntegerOperator::Factorial(factorial)) => {
                let arg = Self::try_from_obj(&factorial.arg)?;
                if !factorial_arg_ok(&arg) {
                    return None;
                }
                Some(ClosedNumericExpr::Factorial(Box::new(arg)))
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(sqrt)) => Some(ClosedNumericExpr::Sqrt(
                Box::new(Self::try_from_obj(&sqrt.arg)?),
            )),
            Obj::ExpLogOperator(ExpLogOperator::Log(log)) => Some(ClosedNumericExpr::Log {
                base: Box::new(Self::try_from_obj(&log.base)?),
                arg: Box::new(Self::try_from_obj(&log.arg)?),
            }),
            _ => None,
        }
    }

    pub fn to_obj(&self) -> Obj {
        match self {
            ClosedNumericExpr::Number(n) => Obj::Literal(Literal::Number(n.clone())),
            ClosedNumericExpr::Add(left, right) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Sub(left, right) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Neg(arg) => Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
                arg: Box::new(arg.to_obj()),
            })),
            ClosedNumericExpr::Mul(left, right) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Div(left, right) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Pow { base, exponent } => {
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                    base: Box::new(base.to_obj()),
                    exponent: Box::new(exponent.to_obj()),
                }))
            }
            ClosedNumericExpr::Abs(arg) => Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
                arg: Box::new(arg.to_obj()),
            })),
            ClosedNumericExpr::Min(left, right) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Max(left, right) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Floor(arg) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
                    arg: Box::new(arg.to_obj()),
                }))
            }
            ClosedNumericExpr::Ceil(arg) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Ceil(Ceil {
                    arg: Box::new(arg.to_obj()),
                }))
            }
            ClosedNumericExpr::Sign(arg) => {
                Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
                    arg: Box::new(arg.to_obj()),
                }))
            }
            ClosedNumericExpr::Mod(left, right) => {
                Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Quot(left, right) => {
                Obj::IntegerOperator(IntegerOperator::Quot(Quot {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Gcd(left, right) => {
                Obj::IntegerOperator(IntegerOperator::Gcd(Gcd {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Lcm(left, right) => {
                Obj::IntegerOperator(IntegerOperator::Lcm(Lcm {
                    left: Box::new(left.to_obj()),
                    right: Box::new(right.to_obj()),
                }))
            }
            ClosedNumericExpr::Factorial(arg) => {
                Obj::IntegerOperator(IntegerOperator::Factorial(Factorial {
                    arg: Box::new(arg.to_obj()),
                }))
            }
            ClosedNumericExpr::Sqrt(arg) => Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
                arg: Box::new(arg.to_obj()),
            })),
            ClosedNumericExpr::Log { base, arg } => {
                Obj::ExpLogOperator(ExpLogOperator::Log(Log {
                    base: Box::new(base.to_obj()),
                    arg: Box::new(arg.to_obj()),
                }))
            }
        }
    }
}

// Predicate form of classification (same meaning as `try_from_obj(...).is_some()`).
pub fn is_closed_numeric_expr(obj: &Obj) -> bool {
    ClosedNumericExpr::try_from_obj(obj).is_some()
}

fn evaluated_normalized(expr: &ClosedNumericExpr) -> Option<String> {
    evaluate_obj_to_normalized_decimal_number(&expr.to_obj())
        .map(|n| normalize_decimal_number_string(&n.normalized_value))
}

fn both_evaluate_to_integers(left: &ClosedNumericExpr, right: &ClosedNumericExpr) -> bool {
    match (evaluated_normalized(left), evaluated_normalized(right)) {
        (Some(l), Some(r)) => {
            normalized_decimal_str_is_integer(&l) && normalized_decimal_str_is_integer(&r)
        }
        _ => false,
    }
}

fn integer_mod_operands_ok(left: &ClosedNumericExpr, right: &ClosedNumericExpr) -> bool {
    match (evaluated_normalized(left), evaluated_normalized(right)) {
        (Some(l), Some(r)) => {
            normalized_decimal_str_is_integer(&l)
                && normalized_decimal_str_is_integer(&r)
                && r != "0"
        }
        _ => false,
    }
}

fn integer_quot_operands_ok(left: &ClosedNumericExpr, right: &ClosedNumericExpr) -> bool {
    match (evaluated_normalized(left), evaluated_normalized(right)) {
        (Some(l), Some(r)) => {
            normalized_decimal_str_is_integer(&l)
                && normalized_decimal_str_is_non_negative_integer(&r)
                && r != "0"
        }
        _ => false,
    }
}

fn factorial_arg_ok(arg: &ClosedNumericExpr) -> bool {
    match evaluated_normalized(arg) {
        Some(v) => normalized_decimal_str_is_non_negative_integer(&v),
        None => false,
    }
}
