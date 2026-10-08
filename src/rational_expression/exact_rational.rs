use super::integer_factorization::factor_positive_integer;
use crate::ast::obj::{
    ArithmeticOperator, ComplexOperator, ExpLogOperator, IntegerOperator, Literal, Number, Obj,
};
use crate::rational_expression::helper::{div_objs, obj_from_number};
use crate::rational_expression::NumberCompareResult;
use std::collections::BTreeMap;

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
                base.pow_rational(&exponent)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) => {
                let value = Self::from_obj(&abs.arg)?;
                Self::new(value.numerator.checked_abs()?, value.denominator)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Min(min)) => {
                let left = Self::from_obj(&min.left)?;
                let right = Self::from_obj(&min.right)?;
                if left.compare(&right)? == NumberCompareResult::Greater {
                    Some(right)
                } else {
                    Some(left)
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Max(max)) => {
                let left = Self::from_obj(&max.left)?;
                let right = Self::from_obj(&max.right)?;
                if left.compare(&right)? == NumberCompareResult::Less {
                    Some(right)
                } else {
                    Some(left)
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(floor)) => {
                let value = Self::from_obj(&floor.arg)?;
                Self::new(value.numerator.checked_div_euclid(value.denominator)?, 1)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(ceil)) => {
                let value = Self::from_obj(&ceil.arg)?;
                let floor = value.numerator.checked_div_euclid(value.denominator)?;
                let ceil = if value.numerator % value.denominator == 0 {
                    floor
                } else {
                    floor.checked_add(1)?
                };
                Self::new(ceil, 1)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(sign)) => {
                Self::new(Self::from_obj(&sign.arg)?.numerator.signum(), 1)
            }
            Obj::IntegerOperator(operator) => exact_integer_operator(operator),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(sqrt)) => {
                Self::from_obj(&sqrt.arg)?.exact_sqrt()
            }
            Obj::ExpLogOperator(ExpLogOperator::Log(log)) => {
                let base = Self::from_obj(&log.base)?;
                let argument = Self::from_obj(&log.arg)?;
                exact_rational_log(&base, &argument)
            }
            Obj::ExpLogOperator(ExpLogOperator::Exp(exp)) => {
                if !Self::from_obj(&exp.arg)?.is_zero() {
                    return None;
                }
                Self::new(1, 1)
            }
            Obj::ExpLogOperator(ExpLogOperator::Ln(ln)) => {
                if Self::from_obj(&ln.arg)? != Self::new(1, 1)? {
                    return None;
                }
                Self::new(0, 1)
            }
            Obj::ComplexOperator(ComplexOperator::RealPart(part)) => {
                Some(super::exact_complex::exact_complex_coordinates(&part.arg)?.0)
            }
            Obj::ComplexOperator(ComplexOperator::ImaginaryPart(part)) => {
                Some(super::exact_complex::exact_complex_coordinates(&part.arg)?.1)
            }
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(abs)) => {
                super::exact_complex::exact_modulus_radicand(&abs.arg)?
                    .2
                    .exact_sqrt()
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

    // For reduced p/q and positive reduced a/b, a rational result requires
    // exact q-th roots of both a and b. Example: (8/27)^(2/3) = 4/9.
    // Root first, then checked integer power: an overflowing a^p is unnecessary.
    fn pow_rational(&self, exponent: &Self) -> Option<Self> {
        if exponent.denominator == 1 {
            return self.pow_integer(exponent.numerator);
        }
        if self.numerator <= 0 {
            return None;
        }
        let root = Self::new(
            integer_nth_root(self.numerator, exponent.denominator)?,
            integer_nth_root(self.denominator, exponent.denominator)?,
        )?;
        root.pow_integer(exponent.numerator)
    }

    pub(crate) fn compare(&self, other: &Self) -> Option<NumberCompareResult> {
        let common = gcd_i128(self.denominator, other.denominator)?;
        let left = self.numerator.checked_mul(other.denominator / common)?;
        let right = other.numerator.checked_mul(self.denominator / common)?;
        Some(if left < right {
            NumberCompareResult::Less
        } else if left > right {
            NumberCompareResult::Greater
        } else {
            NumberCompareResult::Equal
        })
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.numerator == 0
    }

    pub(crate) fn is_negative(&self) -> bool {
        self.numerator < 0
    }

    pub(crate) fn parts(&self) -> (i128, i128) {
        (self.numerator, self.denominator)
    }

    pub(crate) fn modulo_integer(&self, period: i128) -> Option<Self> {
        if period <= 0 {
            return None;
        }
        let modulus = self.denominator.checked_mul(period)?;
        Self::new(self.numerator.rem_euclid(modulus), self.denominator)
    }

    pub(crate) fn exact_sqrt(&self) -> Option<Self> {
        if self.is_negative() {
            return None;
        }
        Self::new(
            integer_square_root(self.numerator)?,
            integer_square_root(self.denominator)?,
        )
    }
}

pub(crate) fn integer_square_root(value: i128) -> Option<i128> {
    if value < 0 {
        return None;
    }
    if value < 2 {
        return Some(value);
    }
    let mut low = 1;
    let mut high = value;
    while low <= high {
        let middle = low + (high - low) / 2;
        let quotient = value / middle;
        if quotient == middle && value % middle == 0 {
            return Some(middle);
        }
        if middle > quotient {
            high = middle - 1;
        } else {
            low = middle + 1;
        }
    }
    None
}

// Exact positive integer roots, without factoring or floating approximation.
// A checked-power overflow is above every positive i128 input, so binary
// search can safely lower its upper bound. The search takes at most 127 steps.
fn integer_nth_root(value: i128, degree: i128) -> Option<i128> {
    if value < 0 || degree < 1 {
        return None;
    }
    if value < 2 || degree == 1 {
        return Some(value);
    }
    if degree == 2 {
        return integer_square_root(value);
    }
    // For value >= 2, a root would be >= 2; 2^127 exceeds i128::MAX.
    if degree >= 127 {
        return None;
    }
    let degree = u32::try_from(degree).ok()?;
    let mut low = 1;
    let mut high = value;
    while low <= high {
        let middle = low + (high - low) / 2;
        match middle.checked_pow(degree) {
            Some(power) if power == value => return Some(middle),
            Some(power) if power < value => low = middle + 1,
            _ => high = middle - 1,
        }
    }
    None
}

// Integer-only operations accept a rational syntax tree only when its exact
// value is integral. Example: gcd((1/3)*6,8)=2; gcd(1/3,8) stays undefined.
fn exact_integer_operator(operator: &IntegerOperator) -> Option<EvalRational> {
    let integer = |obj: &Obj| EvalRational::from_obj(obj)?.to_i128_if_integer();
    let value = match operator {
        IntegerOperator::Mod(value) => {
            integer(&value.left)?.checked_rem_euclid(integer(&value.right)?)?
        }
        IntegerOperator::Quot(value) => {
            let divisor = integer(&value.right)?;
            if divisor <= 0 {
                return None;
            }
            integer(&value.left)?.checked_div_euclid(divisor)?
        }
        IntegerOperator::Gcd(value) => {
            let left = integer(&value.left)?;
            let right = integer(&value.right)?;
            if left == 0 && right == 0 {
                return None;
            }
            gcd_i128(left, right)?
        }
        IntegerOperator::Lcm(value) => {
            let left = integer(&value.left)?;
            let right = integer(&value.right)?;
            if left == 0 || right == 0 {
                0
            } else {
                (left / gcd_i128(left, right)?)
                    .checked_mul(right)?
                    .checked_abs()?
            }
        }
        IntegerOperator::Factorial(value) => {
            let argument = integer(&value.arg)?;
            if argument < 0 {
                return None;
            }
            let mut product = 1i128;
            for factor in 2..=argument {
                product = product.checked_mul(factor)?;
            }
            product
        }
    };
    EvalRational::new(value, 1)
}

// Positive rational numbers have unique prime valuations. log(b,x)=r exactly
// when every valuation of x is r times that of b, with b>0, b!=1, x>0.
// Example: log(8,4)=2/3; log(1/3,27)=-3. No approximate log or search premises.
fn exact_rational_log(base: &EvalRational, argument: &EvalRational) -> Option<EvalRational> {
    if base.numerator <= 0 || argument.numerator <= 0 || base.numerator == base.denominator {
        return None;
    }
    if argument.numerator == argument.denominator {
        return EvalRational::new(0, 1);
    }
    if base == argument {
        return EvalRational::new(1, 1);
    }
    let valuations = |value: &EvalRational| -> Option<BTreeMap<i128, i128>> {
        let mut result = BTreeMap::new();
        for (prime, exponent) in factor_positive_integer(value.numerator)? {
            result.insert(prime, exponent);
        }
        for (prime, exponent) in factor_positive_integer(value.denominator)? {
            result.insert(prime, -exponent);
        }
        Some(result)
    };
    let base_factors = valuations(base)?;
    let argument_factors = valuations(argument)?;
    let (&prime, &base_exponent) = base_factors.iter().next()?;
    let ratio = EvalRational::new(*argument_factors.get(&prime).unwrap_or(&0), base_exponent)?;
    for (&prime, &exponent) in &base_factors {
        let argument_exponent = *argument_factors.get(&prime).unwrap_or(&0);
        if ratio.numerator.checked_mul(exponent)?
            != ratio.denominator.checked_mul(argument_exponent)?
        {
            return None;
        }
    }
    if argument_factors
        .keys()
        .any(|prime| !base_factors.contains_key(prime))
    {
        return None;
    }
    Some(ratio)
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
