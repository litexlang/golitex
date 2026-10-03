//! Canonical finite rational linear combinations of square-free square roots.
use super::exact_rational::{integer_square_root, EvalRational};
use super::integer_factorization::factor_positive_integer;
use crate::ast::obj::{
    Add, ArithmeticOperator as A, ExpLogOperator, Mul, Neg, Number, Obj, Sqrt, Sub,
};
use crate::rational_expression::helper::obj_from_number;
use std::collections::BTreeMap;

const MAX_TERMS: usize = 64;
const MAX_DEPTH: usize = 64;

// Each positive key is square-free; key 1 is the rational part. Zero
// coefficients are removed. Distinct such roots are Q-linearly independent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExactRadical {
    terms: BTreeMap<i128, EvalRational>,
}

impl ExactRadical {
    pub(crate) fn from_obj(obj: &Obj) -> Option<Self> {
        Self::from_obj_at_depth(obj, 0)
    }

    fn from_obj_at_depth(obj: &Obj, depth: usize) -> Option<Self> {
        if depth > MAX_DEPTH {
            return None;
        }
        if let Some(value) = EvalRational::from_obj(obj) {
            let mut result = Self {
                terms: BTreeMap::new(),
            };
            result.add_term(1, value)?;
            return Some(result);
        }
        match obj {
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) => {
                let value = EvalRational::from_obj(&root.arg)?;
                let (numerator, denominator) = value.parts();
                if numerator < 0 {
                    return None;
                }
                let (a, n) = square_factor(numerator)?;
                let (b, d) = square_factor(denominator)?;
                let coefficient = EvalRational::new(a, b.checked_mul(d)?)?;
                let mut result = Self {
                    terms: BTreeMap::new(),
                };
                result.add_term(n.checked_mul(d)?, coefficient)?;
                Some(result)
            }
            Obj::ArithmeticOperator(A::Neg(value)) => {
                Self::from_obj_at_depth(&value.arg, depth + 1)?.negate()
            }
            Obj::ArithmeticOperator(A::Add(value)) => {
                let left = Self::from_obj_at_depth(&value.left, depth + 1)?;
                let right = Self::from_obj_at_depth(&value.right, depth + 1)?;
                left.add(&right)
            }
            Obj::ArithmeticOperator(A::Sub(value)) => {
                let left = Self::from_obj_at_depth(&value.left, depth + 1)?;
                let right = Self::from_obj_at_depth(&value.right, depth + 1)?.negate()?;
                left.add(&right)
            }
            Obj::ArithmeticOperator(A::Mul(value)) => {
                let left = Self::from_obj_at_depth(&value.left, depth + 1)?;
                let right = Self::from_obj_at_depth(&value.right, depth + 1)?;
                left.multiply(&right)
            }
            Obj::ArithmeticOperator(A::Div(value)) => {
                let left = Self::from_obj_at_depth(&value.left, depth + 1)?;
                let right = Self::from_obj_at_depth(&value.right, depth + 1)?.reciprocal()?;
                left.multiply(&right)
            }
            Obj::ArithmeticOperator(A::Pow(value)) => {
                let base = Self::from_obj_at_depth(&value.base, depth + 1)?;
                let exponent = EvalRational::from_obj(&value.exponent)?.to_i128_if_integer()?;
                base.power(exponent)
            }
            _ => None,
        }
    }

    pub(crate) fn to_obj(&self) -> Obj {
        let mut sum = None;
        for (&radicand, coefficient) in &self.terms {
            let (numerator, denominator) = coefficient.parts();
            let magnitude =
                EvalRational::new(numerator.checked_abs().unwrap(), denominator).unwrap();
            let term = if radicand == 1 {
                magnitude.to_obj()
            } else {
                let root = Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
                    arg: Box::new(number(radicand)),
                }));
                if magnitude == EvalRational::new(1, 1).unwrap() {
                    root
                } else {
                    Obj::ArithmeticOperator(A::Mul(Mul {
                        left: Box::new(magnitude.to_obj()),
                        right: Box::new(root),
                    }))
                }
            };
            sum = Some(match sum {
                None if numerator < 0 => Obj::ArithmeticOperator(A::Neg(Neg {
                    arg: Box::new(term),
                })),
                None => term,
                Some(left) if numerator < 0 => Obj::ArithmeticOperator(A::Sub(Sub {
                    left: Box::new(left),
                    right: Box::new(term),
                })),
                Some(left) => Obj::ArithmeticOperator(A::Add(Add {
                    left: Box::new(left),
                    right: Box::new(term),
                })),
            });
        }
        sum.unwrap_or_else(|| number(0))
    }

    fn add_term(&mut self, radicand: i128, coefficient: EvalRational) -> Option<()> {
        let value = match self.terms.get(&radicand) {
            Some(previous) => previous.add(&coefficient)?,
            None => coefficient,
        };
        if value.is_zero() {
            self.terms.remove(&radicand);
        } else {
            self.terms.insert(radicand, value);
        }
        (self.terms.len() <= MAX_TERMS).then_some(())
    }

    fn add(&self, right: &Self) -> Option<Self> {
        let mut result = self.clone();
        for (&radicand, coefficient) in &right.terms {
            result.add_term(radicand, coefficient.clone())?;
        }
        Some(result)
    }

    fn negate(&self) -> Option<Self> {
        let zero = EvalRational::new(0, 1)?;
        let mut result = Self {
            terms: BTreeMap::new(),
        };
        for (&radicand, coefficient) in &self.terms {
            result.add_term(radicand, zero.sub(coefficient)?)?;
        }
        Some(result)
    }

    fn multiply(&self, right: &Self) -> Option<Self> {
        let mut result = Self {
            terms: BTreeMap::new(),
        };
        for (&a, ca) in &self.terms {
            for (&b, cb) in &right.terms {
                let mut x = a;
                let mut y = b;
                while y != 0 {
                    let remainder = x % y;
                    x = y;
                    y = remainder;
                }
                let radicand = (a / x).checked_mul(b / x)?;
                let coefficient = ca.mul(cb)?.mul(&EvalRational::new(x, 1)?)?;
                result.add_term(radicand, coefficient)?;
            }
        }
        Some(result)
    }

    // Only one radical term in the denominator is normalized here:
    // 1/(c*sqrt(d)) = sqrt(d)/(c*d). General radical-field inversion is excluded.
    fn reciprocal(&self) -> Option<Self> {
        if self.terms.len() != 1 {
            return None;
        }
        let (&radicand, coefficient) = self.terms.iter().next()?;
        let denominator = coefficient.mul(&EvalRational::new(radicand, 1)?)?;
        let mut result = Self {
            terms: BTreeMap::new(),
        };
        result.add_term(radicand, EvalRational::new(1, 1)?.div(&denominator)?)?;
        Some(result)
    }

    fn power(&self, exponent: i128) -> Option<Self> {
        let mut magnitude = usize::try_from(exponent.checked_abs()?).ok()?;
        let mut base = if exponent < 0 {
            self.reciprocal()?
        } else {
            self.clone()
        };
        let mut value = Self::from_obj(&number(1))?;
        while magnitude != 0 {
            if magnitude & 1 != 0 {
                value = value.multiply(&base)?;
            }
            magnitude >>= 1;
            if magnitude != 0 {
                base = base.multiply(&base)?;
            }
        }
        Some(value)
    }
}

fn square_factor(value: i128) -> Option<(i128, i128)> {
    if let Some(root) = integer_square_root(value) {
        return Some((root, 1));
    }
    let mut square = 1i128;
    let mut square_free = 1i128;
    for (prime, exponent) in factor_positive_integer(value)? {
        square = square.checked_mul(prime.checked_pow(u32::try_from(exponent / 2).ok()?)?)?;
        if exponent % 2 != 0 {
            square_free = square_free.checked_mul(prime)?;
        }
    }
    Some((square, square_free))
}

fn number(value: i128) -> Obj {
    obj_from_number(Number::new(value.to_string()))
}
