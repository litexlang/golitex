use crate::ast::obj::{Number, Obj, ArithmeticOperator, Literal};
use crate::rational_expression::NumberCompareResult;
use crate::rational_expression::helper::{div_objs, obj_from_number};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalRational {
    numerator: i128,
    denominator: i128,
}

impl EvalRational {
    pub fn new(numerator: i128, denominator: i128) -> Option<Self> {
        if denominator == 0 {
            return None;
        }
        let mut numerator = numerator;
        let mut denominator = denominator;
        if denominator < 0 {
            numerator = numerator.checked_neg()?;
            denominator = denominator.checked_neg()?;
        }
        let common_factor = gcd_i128(numerator, denominator)?;
        Some(EvalRational {
            numerator: numerator / common_factor,
            denominator: denominator / common_factor,
        })
    }

    pub fn from_obj(obj: &Obj) -> Option<Self> {
        match obj {
            Obj::Literal(Literal::Number(number)) => Self::from_number(number),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) => {
                let left = Self::from_obj(&add.left)?;
                let right = Self::from_obj(&add.right)?;
                left.add(&right)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) => {
                let left = Self::from_obj(&sub.left)?;
                let right = Self::from_obj(&sub.right)?;
                left.sub(&right)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) => {
                let arg = Self::from_obj(&neg.arg)?;
                Self::new(0, 1)?.sub(&arg)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) => {
                let left = Self::from_obj(&mul.left)?;
                let right = Self::from_obj(&mul.right)?;
                left.mul(&right)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) => {
                let left = Self::from_obj(&div.left)?;
                let right = Self::from_obj(&div.right)?;
                left.div(&right)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)) => {
                let base = Self::from_obj(&pow.base)?;
                let exponent = Self::from_obj(&pow.exponent)?;
                base.pow_integer(exponent.to_i128_if_integer()?)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) => {
                let value = Self::from_obj(&abs.arg)?;
                Self::new(value.numerator.checked_abs()?, value.denominator)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Min(min)) => {
                let left = Self::from_obj(&min.left)?;
                let right = Self::from_obj(&min.right)?;
                if left.compare(&right)? == NumberCompareResult::Greater { Some(right) } else { Some(left) }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Max(max)) => {
                let left = Self::from_obj(&max.left)?;
                let right = Self::from_obj(&max.right)?;
                if left.compare(&right)? == NumberCompareResult::Less { Some(right) } else { Some(left) }
            }
            _ => None,
        }
    }

    pub fn to_obj(&self) -> Obj {
        if self.denominator == 1 {
            return obj_from_number(Number::new(self.numerator.to_string()));
        }
        div_objs(
            obj_from_number(Number::new(self.numerator.to_string())),
            obj_from_number(Number::new(self.denominator.to_string())),
        )
    }

    pub fn to_i128_if_integer(&self) -> Option<i128> {
        if self.denominator == 1 {
            Some(self.numerator)
        } else {
            None
        }
    }

    fn from_number(number: &Number) -> Option<Self> {
        Self::from_decimal_str(&number.normalized_value)
    }

    fn from_decimal_str(number_string: &str) -> Option<Self> {
        let trimmed_number_string = number_string.trim();
        if trimmed_number_string.is_empty() {
            return None;
        }
        let (is_negative, magnitude_string) =
            if let Some(rest) = trimmed_number_string.strip_prefix('-') {
                (true, rest)
            } else {
                (false, trimmed_number_string)
            };
        let (integer_part, fractional_part) = magnitude_string
            .split_once('.')
            .unwrap_or((magnitude_string, ""));
        if !string_has_only_ascii_digits_or_is_empty(integer_part)
            || !string_has_only_ascii_digits_or_is_empty(fractional_part)
        {
            return None;
        }
        if integer_part.is_empty() && fractional_part.is_empty() {
            return None;
        }

        let denominator = pow10_i128(fractional_part.len())?;
        let integer_value = parse_ascii_digits_to_i128(integer_part)?;
        let fractional_value = parse_ascii_digits_to_i128(fractional_part)?;
        let numerator = integer_value
            .checked_mul(denominator)?
            .checked_add(fractional_value)?;
        let numerator = if is_negative {
            numerator.checked_neg()?
        } else {
            numerator
        };
        Self::new(numerator, denominator)
    }

    pub(crate) fn add(&self, other: &Self) -> Option<Self> {
        let left = self.numerator.checked_mul(other.denominator)?;
        let right = other.numerator.checked_mul(self.denominator)?;
        let numerator = left.checked_add(right)?;
        let denominator = self.denominator.checked_mul(other.denominator)?;
        Self::new(numerator, denominator)
    }

    pub(crate) fn sub(&self, other: &Self) -> Option<Self> {
        let left = self.numerator.checked_mul(other.denominator)?;
        let right = other.numerator.checked_mul(self.denominator)?;
        let numerator = left.checked_sub(right)?;
        let denominator = self.denominator.checked_mul(other.denominator)?;
        Self::new(numerator, denominator)
    }

    pub(crate) fn mul(&self, other: &Self) -> Option<Self> {
        let numerator = self.numerator.checked_mul(other.numerator)?;
        let denominator = self.denominator.checked_mul(other.denominator)?;
        Self::new(numerator, denominator)
    }

    pub(crate) fn div(&self, other: &Self) -> Option<Self> {
        if other.numerator == 0 {
            return None;
        }
        let numerator = self.numerator.checked_mul(other.denominator)?;
        let denominator = self.denominator.checked_mul(other.numerator)?;
        Self::new(numerator, denominator)
    }

    fn pow(&self, exponent: usize) -> Option<Self> {
        let mut acc = EvalRational::new(1, 1)?;
        let mut base = self.clone();
        let mut exponent = exponent;
        while exponent > 0 {
            if exponent % 2 == 1 {
                acc = acc.mul(&base)?;
            }
            exponent /= 2;
            if exponent > 0 {
                base = base.mul(&base)?;
            }
        }
        Some(acc)
    }

    // A negative integer power is the positive power of the reciprocal.
    // Example: 3^(-2) = 1/9. Zero and checked arithmetic overflow fail closed.
    pub(crate) fn pow_integer(&self, exponent: i128) -> Option<Self> {
        let magnitude = usize::try_from(exponent.checked_abs()?).ok()?;
        if exponent < 0 {
            Self::new(self.denominator, self.numerator)?.pow(magnitude)
        } else {
            self.pow(magnitude)
        }
    }

    pub(crate) fn compare(&self, other: &Self) -> Option<NumberCompareResult> {
        let common = gcd_i128(self.denominator, other.denominator)?;
        let left = self.numerator.checked_mul(other.denominator / common)?;
        let right = other.numerator.checked_mul(self.denominator / common)?;
        Some(if left < right { NumberCompareResult::Less } else if left > right { NumberCompareResult::Greater } else { NumberCompareResult::Equal })
    }

    pub(crate) fn is_zero(&self) -> bool { self.numerator == 0 }

    pub(crate) fn is_negative(&self) -> bool { self.numerator < 0 }

    pub(crate) fn parts(&self) -> (i128, i128) { (self.numerator, self.denominator) }

    pub(crate) fn modulo_integer(&self, period: i128) -> Option<Self> {
        let modulus = self.denominator.checked_mul(period)?;
        Self::new(self.numerator.rem_euclid(modulus), self.denominator)
    }

    pub(crate) fn exact_sqrt(&self) -> Option<Self> {
        if self.is_negative() { return None; }
        Self::new(integer_square_root(self.numerator)?, integer_square_root(self.denominator)?)
    }
}

fn integer_square_root(value: i128) -> Option<i128> {
    if value < 0 { return None; }
    if value < 2 { return Some(value); }
    let mut low = 1;
    let mut high = value;
    while low <= high {
        let middle = low + (high - low) / 2;
        let quotient = value / middle;
        if quotient == middle && value % middle == 0 { return Some(middle); }
        if middle > quotient { high = middle - 1; } else { low = middle + 1; }
    }
    None
}

pub fn evaluate_obj_to_exact_rational_for_eval(obj: &Obj) -> Option<EvalRational> {
    EvalRational::from_obj(obj)
}

pub fn evaluate_obj_to_exact_rational_obj_for_eval(obj: &Obj) -> Option<Obj> {
    EvalRational::from_obj(obj).map(|rational| rational.to_obj())
}

fn gcd_i128(mut left: i128, mut right: i128) -> Option<i128> {
    left = left.checked_abs()?;
    right = right.checked_abs()?;
    while right != 0 {
        let next_right = left % right;
        left = right;
        right = next_right;
    }
    if left == 0 {
        Some(1)
    } else {
        Some(left)
    }
}

fn string_has_only_ascii_digits_or_is_empty(s: &str) -> bool {
    s.chars().all(|c| c.is_ascii_digit())
}

fn parse_ascii_digits_to_i128(s: &str) -> Option<i128> {
    let mut result = 0_i128;
    for c in s.chars() {
        let digit = c.to_digit(10)? as i128;
        result = result.checked_mul(10)?.checked_add(digit)?;
    }
    Some(result)
}

fn pow10_i128(exponent: usize) -> Option<i128> {
    let mut result = 1_i128;
    for _ in 0..exponent {
        result = result.checked_mul(10)?;
    }
    Some(result)
}
