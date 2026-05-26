use crate::prelude::*;

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
            Obj::Number(number) => Self::from_number(number),
            Obj::Add(add) => {
                let left = Self::from_obj(&add.left)?;
                let right = Self::from_obj(&add.right)?;
                left.add(&right)
            }
            Obj::Sub(sub) => {
                let left = Self::from_obj(&sub.left)?;
                let right = Self::from_obj(&sub.right)?;
                left.sub(&right)
            }
            Obj::Mul(mul) => {
                let left = Self::from_obj(&mul.left)?;
                let right = Self::from_obj(&mul.right)?;
                left.mul(&right)
            }
            Obj::Div(div) => {
                let left = Self::from_obj(&div.left)?;
                let right = Self::from_obj(&div.right)?;
                left.div(&right)
            }
            Obj::Pow(pow) => {
                let base = Self::from_obj(&pow.base)?;
                let exponent = Self::from_obj(&pow.exponent)?;
                let exponent = exponent.to_non_negative_usize_if_integer()?;
                base.pow(exponent)
            }
            _ => None,
        }
    }

    pub fn to_obj(&self) -> Obj {
        if self.denominator == 1 {
            return Number::new(self.numerator.to_string()).into();
        }
        Div::new(
            Number::new(self.numerator.to_string()).into(),
            Number::new(self.denominator.to_string()).into(),
        )
        .into()
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

    fn add(&self, other: &Self) -> Option<Self> {
        let left = self.numerator.checked_mul(other.denominator)?;
        let right = other.numerator.checked_mul(self.denominator)?;
        let numerator = left.checked_add(right)?;
        let denominator = self.denominator.checked_mul(other.denominator)?;
        Self::new(numerator, denominator)
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        let left = self.numerator.checked_mul(other.denominator)?;
        let right = other.numerator.checked_mul(self.denominator)?;
        let numerator = left.checked_sub(right)?;
        let denominator = self.denominator.checked_mul(other.denominator)?;
        Self::new(numerator, denominator)
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        let numerator = self.numerator.checked_mul(other.numerator)?;
        let denominator = self.denominator.checked_mul(other.denominator)?;
        Self::new(numerator, denominator)
    }

    fn div(&self, other: &Self) -> Option<Self> {
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
            base = base.mul(&base)?;
            exponent /= 2;
        }
        Some(acc)
    }

    fn to_non_negative_usize_if_integer(&self) -> Option<usize> {
        if self.denominator != 1 || self.numerator < 0 {
            return None;
        }
        usize::try_from(self.numerator).ok()
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_rational_eval_keeps_non_terminating_division() {
        let obj: Obj = Add::new(
            Number::new("1".to_string()).into(),
            Div::new(
                Number::new("1".to_string()).into(),
                Number::new("3".to_string()).into(),
            )
            .into(),
        )
        .into();
        let rational_obj = evaluate_obj_to_exact_rational_obj_for_eval(&obj).unwrap();
        assert_eq!(rational_obj.to_string(), "4 / 3");
    }

    #[test]
    fn exact_rational_eval_reduces_decimal_and_fraction_mix() {
        let obj: Obj = Div::new(
            Number::new("1.5".to_string()).into(),
            Number::new("3".to_string()).into(),
        )
        .into();
        let rational_obj = evaluate_obj_to_exact_rational_obj_for_eval(&obj).unwrap();
        assert_eq!(rational_obj.to_string(), "1 / 2");
    }
}
