use crate::algebraic_normalization::exact_division::safe_div;
use crate::object::range_cardinality::{
    count_closed_range_integer_endpoints, count_half_open_range_integer_endpoints,
};
use crate::prelude::*;

impl Obj {
    pub fn evaluate_to_normalized_decimal_number(&self) -> Option<Number> {
        self.evaluate_to_normalized_decimal_number_with_result()
            .map(|result| result.value)
    }

    pub fn evaluate_to_normalized_decimal_number_with_result(
        &self,
    ) -> Option<SuccessEvaluateObjResult> {
        let (value, step) = match self {
            Obj::Number(number) => return Some(SuccessEvaluateObjResult::literal(number.clone())),
            Obj::Add(add) => {
                let left = add
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = add
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let a = &left.value.normalized_value;
                let b = &right.value.normalized_value;
                let sum = if normalized_decimal_str_is_non_negative(a)
                    && normalized_decimal_str_is_non_negative(b)
                {
                    // This helper expects both operands to be non-negative.
                    add_decimal_str_and_normalize(a, b)
                } else {
                    add_signed_decimal_str(a, b)
                };
                (
                    Number::new(sum),
                    binary_evaluation_step(EvaluateBinaryObjOperator::Add, left, right),
                )
            }
            Obj::Sub(sub) => {
                let left = sub
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = sub
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let a = &left.value.normalized_value;
                let b = &right.value.normalized_value;
                let difference = if normalized_decimal_str_is_non_negative(a)
                    && normalized_decimal_str_is_non_negative(b)
                {
                    // This helper compares magnitudes and expects non-negative operands.
                    sub_decimal_str_and_normalize(a, b)
                } else {
                    sub_signed_decimal_str(a, b)
                };
                (
                    Number::new(difference),
                    binary_evaluation_step(EvaluateBinaryObjOperator::Sub, left, right),
                )
            }
            Obj::Mul(mul) => {
                let left = mul
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = mul
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = Number::new(mul_signed_decimal_str(
                    &left.value.normalized_value,
                    &right.value.normalized_value,
                ));
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Mul, left, right),
                )
            }
            Obj::Mod(mod_obj) => {
                let left = mod_obj
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = mod_obj
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = Number::new(mod_decimal_str_and_normalize(
                    &left.value.normalized_value,
                    &right.value.normalized_value,
                ));
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Mod, left, right),
                )
            }
            Obj::Quot(quot) => {
                let left = quot
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = quot
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = Number::new(quot_decimal_str_and_normalize(
                    &left.value.normalized_value,
                    &right.value.normalized_value,
                ));
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Quot, left, right),
                )
            }
            Obj::Gcd(gcd) => {
                let left = gcd
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = gcd
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = gcd_decimal_str_and_normalize(
                    &left.value.normalized_value,
                    &right.value.normalized_value,
                )
                .map(Number::new)?;
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Gcd, left, right),
                )
            }
            Obj::Lcm(lcm) => {
                let left = lcm
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = lcm
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = lcm_decimal_str_and_normalize(
                    &left.value.normalized_value,
                    &right.value.normalized_value,
                )
                .map(Number::new)?;
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Lcm, left, right),
                )
            }
            Obj::Floor(floor) => {
                let argument = floor
                    .arg
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = Number::new(floor_decimal_str(&argument.value.normalized_value));
                (
                    value,
                    unary_evaluation_step(EvaluateUnaryObjOperator::Floor, argument),
                )
            }
            Obj::Ceil(ceil) => {
                let argument = ceil
                    .arg
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = Number::new(ceil_decimal_str(&argument.value.normalized_value));
                (
                    value,
                    unary_evaluation_step(EvaluateUnaryObjOperator::Ceil, argument),
                )
            }
            Obj::Min(min) => {
                let left = min
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = min
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = evaluated_min_or_max_value(&left, &right, false);
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Min, left, right),
                )
            }
            Obj::Max(max) => {
                let left = max
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = max
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = evaluated_min_or_max_value(&left, &right, true);
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Max, left, right),
                )
            }
            Obj::Exp(exp) => {
                let argument = exp
                    .arg
                    .evaluate_to_normalized_decimal_number_with_result()?;
                if argument.value.normalized_value != "0" {
                    return None;
                }
                (
                    Number::new("1".to_string()),
                    unary_evaluation_step(EvaluateUnaryObjOperator::Exp, argument),
                )
            }
            Obj::Ln(ln) => {
                let argument = ln.arg.evaluate_to_normalized_decimal_number_with_result()?;
                if argument.value.normalized_value != "1" {
                    return None;
                }
                (
                    Number::new("0".to_string()),
                    unary_evaluation_step(EvaluateUnaryObjOperator::Ln, argument),
                )
            }
            Obj::Sign(sign) => {
                let argument = sign
                    .arg
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = if argument.value.normalized_value == "0" {
                    "0"
                } else if argument.value.normalized_value.starts_with('-') {
                    "-1"
                } else {
                    "1"
                };
                (
                    Number::new(value.to_string()),
                    unary_evaluation_step(EvaluateUnaryObjOperator::Sign, argument),
                )
            }
            Obj::Factorial(factorial) => {
                let argument = factorial
                    .arg
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = factorial_decimal_str_and_normalize(&argument.value.normalized_value)
                    .map(Number::new)?;
                (
                    value,
                    unary_evaluation_step(EvaluateUnaryObjOperator::Factorial, argument),
                )
            }
            Obj::Pow(pow_obj) => {
                let left = pow_obj
                    .base
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = pow_obj
                    .exponent
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = pow_decimal_str_and_normalize(
                    &left.value.normalized_value,
                    &right.value.normalized_value,
                )
                .map(Number::new)?;
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Pow, left, right),
                )
            }
            Obj::Div(div) => {
                let left = div
                    .left
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let right = div
                    .right
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value = safe_div(&left.value.normalized_value, &right.value.normalized_value)
                    .map(Number::new)?;
                (
                    value,
                    binary_evaluation_step(EvaluateBinaryObjOperator::Div, left, right),
                )
            }
            Obj::Abs(abs) => {
                let argument = abs
                    .arg
                    .evaluate_to_normalized_decimal_number_with_result()?;
                let value =
                    if let Some(rest) = argument.value.normalized_value.trim().strip_prefix('-') {
                        Number::new(rest.trim().to_string())
                    } else {
                        argument.value.clone()
                    };
                (
                    value,
                    unary_evaluation_step(EvaluateUnaryObjOperator::Abs, argument),
                )
            }
            Obj::CartDim(cart_dim) => match &*cart_dim.set {
                Obj::Cart(cart) => (
                    Number::new(cart.args.len().to_string()),
                    shape_evaluation_step(
                        EvaluateObjShapeOperator::CartDim,
                        vec![(*cart_dim.set).clone()],
                        vec![],
                    ),
                ),
                _ => return None,
            },
            Obj::TupleDim(tuple_dim) => match &*tuple_dim.arg {
                Obj::Tuple(tuple) => (
                    Number::new(tuple.args.len().to_string()),
                    shape_evaluation_step(
                        EvaluateObjShapeOperator::TupleDim,
                        vec![(*tuple_dim.arg).clone()],
                        vec![],
                    ),
                ),
                _ => return None,
            },
            Obj::FiniteSetSize(finite_set_size) => match &*finite_set_size.set {
                Obj::ListSet(list_set) => (
                    Number::new(list_set.list.len().to_string()),
                    shape_evaluation_step(
                        EvaluateObjShapeOperator::ListSetSize,
                        list_set.list.iter().map(|item| (**item).clone()).collect(),
                        vec![],
                    ),
                ),
                Obj::ClosedRange(cr) => {
                    let start = cr
                        .start
                        .evaluate_to_normalized_decimal_number_with_result()?;
                    let end = cr.end.evaluate_to_normalized_decimal_number_with_result()?;
                    let value = count_closed_range_integer_endpoints(&start.value, &end.value)?;
                    (
                        value,
                        shape_evaluation_step(
                            EvaluateObjShapeOperator::ClosedRangeSize,
                            vec![],
                            vec![start, end],
                        ),
                    )
                }
                Obj::Range(r) => {
                    let start = r
                        .start
                        .evaluate_to_normalized_decimal_number_with_result()?;
                    let end = r.end.evaluate_to_normalized_decimal_number_with_result()?;
                    let value = count_half_open_range_integer_endpoints(&start.value, &end.value)?;
                    (
                        value,
                        shape_evaluation_step(
                            EvaluateObjShapeOperator::RangeSize,
                            vec![],
                            vec![start, end],
                        ),
                    )
                }
                // |A_1 × ... × A_n| = |A_1| * ... * |A_n|; empty product is 1.
                Obj::Cart(cart) => {
                    let mut acc = "1".to_string();
                    let mut evaluated_children = Vec::new();
                    for arg in cart.args.iter() {
                        let factor_finite_set_size =
                            Obj::FiniteSetSize(FiniteSetSize::new((**arg).clone()))
                                .evaluate_to_normalized_decimal_number_with_result()?;
                        acc = mul_signed_decimal_str(
                            acc.trim(),
                            factor_finite_set_size.value.normalized_value.trim(),
                        );
                        evaluated_children.push(factor_finite_set_size);
                    }
                    (
                        Number::new(acc),
                        shape_evaluation_step(
                            EvaluateObjShapeOperator::CartSize,
                            cart.args.iter().map(|arg| (**arg).clone()).collect(),
                            evaluated_children,
                        ),
                    )
                }
                _ => return None,
            },
            Obj::FiniteSetMax(extremum) => {
                let (value, inputs, evaluated_children) =
                    evaluate_nonempty_numeric_list_set_with_result(extremum.set.as_ref(), true)?;
                (
                    value,
                    shape_evaluation_step(
                        EvaluateObjShapeOperator::FiniteSetMax,
                        inputs,
                        evaluated_children,
                    ),
                )
            }
            Obj::FiniteSetMin(extremum) => {
                let (value, inputs, evaluated_children) =
                    evaluate_nonempty_numeric_list_set_with_result(extremum.set.as_ref(), false)?;
                (
                    value,
                    shape_evaluation_step(
                        EvaluateObjShapeOperator::FiniteSetMin,
                        inputs,
                        evaluated_children,
                    ),
                )
            }
            _ => return None,
        };

        Some(SuccessEvaluateObjResult::new(self.clone(), value, step))
    }

    pub fn two_objs_can_be_calculated_and_equal_by_calculation(&self, other: &Obj) -> bool {
        match (
            self.evaluate_to_normalized_decimal_number(),
            other.evaluate_to_normalized_decimal_number(),
        ) {
            (Some(left_number), Some(right_number)) => {
                return left_number.normalized_value == right_number.normalized_value;
            }
            _ => return false,
        }
    }
}

pub fn gcd_decimal_str_and_normalize(left: &str, right: &str) -> Option<String> {
    let normalized_left = normalize_decimal_number_string(left);
    let normalized_right = normalize_decimal_number_string(right);
    if normalized_left.contains('.') || normalized_right.contains('.') {
        return None;
    }
    let mut a = normalized_left
        .strip_prefix('-')
        .unwrap_or(&normalized_left)
        .to_string();
    let mut b = normalized_right
        .strip_prefix('-')
        .unwrap_or(&normalized_right)
        .to_string();
    if a == "0" && b == "0" {
        return None;
    }
    while b != "0" {
        let remainder = mod_decimal_str_and_normalize(&a, &b);
        a = b;
        b = remainder;
    }
    Some(a)
}

pub fn lcm_decimal_str_and_normalize(left: &str, right: &str) -> Option<String> {
    let normalized_left = normalize_decimal_number_string(left);
    let normalized_right = normalize_decimal_number_string(right);
    if normalized_left.contains('.') || normalized_right.contains('.') {
        return None;
    }
    if normalized_left == "0" || normalized_right == "0" {
        return Some("0".to_string());
    }
    let gcd = gcd_decimal_str_and_normalize(&normalized_left, &normalized_right)?;
    let quotient = safe_div(&normalized_left, &gcd)?;
    let product = mul_signed_decimal_str(&quotient, &normalized_right);
    Some(product.strip_prefix('-').unwrap_or(&product).to_string())
}

pub fn factorial_decimal_str_and_normalize(value: &str) -> Option<String> {
    let normalized = normalize_decimal_number_string(value);
    if normalized.starts_with('-') || normalized.contains('.') {
        return None;
    }
    let n = normalized.parse::<usize>().ok()?;
    let mut result = "1".to_string();
    for factor in 2..=n {
        result = mul_signed_decimal_str(&result, &factor.to_string());
    }
    Some(result)
}

fn floor_decimal_str(value: &str) -> String {
    let normalized = normalize_decimal_number_string(value);
    let Some((integer, fraction)) = normalized.split_once('.') else {
        return normalized;
    };
    if normalized.starts_with('-') && fraction.bytes().any(|digit| digit != b'0') {
        let magnitude = integer.strip_prefix('-').unwrap_or(integer);
        return format!("-{}", add_decimal_str_and_normalize(magnitude, "1"));
    }
    integer.to_string()
}

fn ceil_decimal_str(value: &str) -> String {
    let normalized = normalize_decimal_number_string(value);
    let Some((integer, fraction)) = normalized.split_once('.') else {
        return normalized;
    };
    if fraction.bytes().all(|digit| digit == b'0') {
        return integer.to_string();
    }
    if normalized.starts_with('-') {
        return integer.to_string();
    }
    add_decimal_str_and_normalize(integer, "1")
}

fn unary_evaluation_step(
    operator: EvaluateUnaryObjOperator,
    argument: SuccessEvaluateObjResult,
) -> SuccessEvaluateObjStepResult {
    SuccessEvaluateObjStepResult::Unary(Box::new(SuccessEvaluateUnaryObjResult::new(
        operator, argument,
    )))
}

fn binary_evaluation_step(
    operator: EvaluateBinaryObjOperator,
    left: SuccessEvaluateObjResult,
    right: SuccessEvaluateObjResult,
) -> SuccessEvaluateObjStepResult {
    SuccessEvaluateObjStepResult::Binary(Box::new(SuccessEvaluateBinaryObjResult::new(
        operator, left, right,
    )))
}

fn shape_evaluation_step(
    operator: EvaluateObjShapeOperator,
    inputs: Vec<Obj>,
    evaluated_children: Vec<SuccessEvaluateObjResult>,
) -> SuccessEvaluateObjStepResult {
    SuccessEvaluateObjStepResult::Shape(Box::new(SuccessEvaluateObjByShapeResult::new(
        operator,
        inputs,
        evaluated_children,
    )))
}

fn evaluated_min_or_max_value(
    left: &SuccessEvaluateObjResult,
    right: &SuccessEvaluateObjResult,
    take_maximum: bool,
) -> Number {
    let difference = sub_signed_decimal_str(
        right.value.normalized_value.trim(),
        left.value.normalized_value.trim(),
    );
    let right_is_larger = !difference.trim().starts_with('-') && difference.trim() != "0";
    if right_is_larger == take_maximum {
        right.value.clone()
    } else {
        left.value.clone()
    }
}

fn evaluate_nonempty_numeric_list_set_with_result(
    set: &Obj,
    take_maximum: bool,
) -> Option<(Number, Vec<Obj>, Vec<SuccessEvaluateObjResult>)> {
    let Obj::ListSet(list_set) = set else {
        return None;
    };
    let inputs = list_set
        .list
        .iter()
        .map(|element| (**element).clone())
        .collect::<Vec<_>>();
    let mut evaluated_children = Vec::new();
    for element in list_set.list.iter() {
        evaluated_children.push(element.evaluate_to_normalized_decimal_number_with_result()?);
    }
    let mut result = evaluated_children.first()?.value.clone();
    for candidate in evaluated_children.iter().skip(1) {
        let difference = sub_signed_decimal_str(
            candidate.value.normalized_value.trim(),
            result.normalized_value.trim(),
        );
        let candidate_is_larger = !difference.trim().starts_with('-') && difference.trim() != "0";
        if candidate_is_larger == take_maximum {
            result = candidate.value.clone();
        }
    }
    Some((result, inputs, evaluated_children))
}

/// Returns whether a normalized decimal string is non-negative.
fn normalized_decimal_str_is_non_negative(s: &str) -> bool {
    !s.trim().starts_with('-')
}

fn split_sign_and_magnitude(number_string: &str) -> (bool, String) {
    let trimmed_number_string = number_string.trim();
    if let Some(stripped_number_string) = trimmed_number_string.strip_prefix('-') {
        (true, stripped_number_string.trim().to_string())
    } else {
        (false, trimmed_number_string.to_string())
    }
}

pub fn mul_signed_decimal_str(left_number_string: &str, right_number_string: &str) -> String {
    let (left_is_negative, left_magnitude_number_string) =
        split_sign_and_magnitude(left_number_string);
    let (right_is_negative, right_magnitude_number_string) =
        split_sign_and_magnitude(right_number_string);
    let multiplied_magnitude_number_string = mul_decimal_str_and_normalize(
        &left_magnitude_number_string,
        &right_magnitude_number_string,
    );
    let multiplied_magnitude_is_zero = multiplied_magnitude_number_string == "0";
    let multiplied_result_is_negative = left_is_negative ^ right_is_negative;
    if multiplied_result_is_negative && !multiplied_magnitude_is_zero {
        normalize_decimal_number_string(&format!("-{}", multiplied_magnitude_number_string))
    } else {
        normalize_decimal_number_string(&multiplied_magnitude_number_string)
    }
}

/// Adds signed decimal strings; magnitude addition only handles non-negative operands.
pub fn add_signed_decimal_str(a: &str, b: &str) -> String {
    let (a_neg, a_mag) = split_sign_and_magnitude(a);
    let (b_neg, b_mag) = split_sign_and_magnitude(b);
    match (a_neg, b_neg) {
        (false, false) => add_decimal_str_and_normalize(&a_mag, &b_mag),
        (true, true) => {
            let sum_mag = add_decimal_str_and_normalize(&a_mag, &b_mag);
            if sum_mag == "0" {
                "0".to_string()
            } else {
                normalize_decimal_number_string(&format!("-{}", sum_mag))
            }
        }
        (false, true) => sub_decimal_str_and_normalize(&a_mag, &b_mag),
        (true, false) => sub_decimal_str_and_normalize(&b_mag, &a_mag),
    }
}

/// Subtracts signed decimal strings.
pub fn sub_signed_decimal_str(a: &str, b: &str) -> String {
    add_signed_decimal_str(a, &mul_signed_decimal_str(b, "-1"))
}

impl Obj {
    pub fn replace_with_numeric_result_if_can_be_calculated(&self) -> (Obj, bool) {
        if let Some(calculated_number) = self.evaluate_to_normalized_decimal_number() {
            (Obj::Number(calculated_number), true)
        } else {
            (self.clone(), false)
        }
    }
}

/// Adds two non-negative decimal strings and returns a normalized sum.
pub fn add_decimal_str_and_normalize(a: &str, b: &str) -> String {
    let (mut int_a, mut frac_a) = parse_decimal_parts(a);
    let (mut int_b, mut frac_b) = parse_decimal_parts(b);
    let frac_len = frac_a.len().max(frac_b.len());
    frac_a.resize(frac_len, 0);
    frac_b.resize(frac_len, 0);
    let int_len = int_a.len().max(int_b.len());
    int_a.reverse();
    int_b.reverse();
    int_a.resize(int_len, 0);
    int_b.resize(int_len, 0);

    let mut out_frac = vec![0u8; frac_len];
    let mut carry = 0u8;
    for i in (0..frac_len).rev() {
        let sum = frac_a[i] + frac_b[i] + carry;
        out_frac[i] = sum % 10;
        carry = sum / 10;
    }
    let mut out_int = Vec::with_capacity(int_len + 1);
    for i in 0..int_len {
        let sum = int_a[i] + int_b[i] + carry;
        out_int.push(sum % 10);
        carry = sum / 10;
    }
    if carry > 0 {
        out_int.push(carry);
    }
    out_int.reverse();

    let int_str: String = out_int.iter().map(|&d| (b'0' + d) as char).collect();
    let frac_str: String = out_frac.iter().map(|&d| (b'0' + d) as char).collect();
    let result = if frac_str.is_empty() || out_frac.iter().all(|&d| d == 0) {
        int_str
    } else {
        format!("{}.{}", int_str, frac_str.trim_end_matches('0'))
    };
    normalize_decimal_number_string(&result)
}

/// Subtracts two non-negative decimal strings and preserves the sign when needed.
pub fn sub_decimal_str_and_normalize(a: &str, b: &str) -> String {
    let (int_a, frac_a) = parse_decimal_parts(a);
    let (int_b, frac_b) = parse_decimal_parts(b);
    let frac_len = frac_a.len().max(frac_b.len());
    let mut fa: Vec<u8> = frac_a.iter().cloned().collect();
    let mut fb: Vec<u8> = frac_b.iter().cloned().collect();
    fa.resize(frac_len, 0);
    fb.resize(frac_len, 0);
    let int_len = int_a.len().max(int_b.len());
    let mut ia: Vec<u8> = int_a.iter().cloned().collect();
    let mut ib: Vec<u8> = int_b.iter().cloned().collect();
    ia.reverse();
    ib.reverse();
    ia.resize(int_len, 0);
    ib.resize(int_len, 0);

    let cmp = compare_decimal_parts(&ia, &fa, &ib, &fb);
    let (top_int, top_frac, bot_int, bot_frac) = if cmp >= 0 {
        (ia, fa, ib, fb)
    } else {
        let inner = sub_decimal_str_and_normalize(b, a);
        return normalize_decimal_number_string(&format!("-{}", inner));
    };

    let mut out_frac = vec![0u8; frac_len];
    let mut borrow: i16 = 0;
    for i in (0..frac_len).rev() {
        let mut d = top_frac[i] as i16 - bot_frac[i] as i16 - borrow;
        borrow = 0;
        if d < 0 {
            d += 10;
            borrow = 1;
        }
        out_frac[i] = d as u8;
    }
    let mut out_int = Vec::with_capacity(int_len);
    for i in 0..int_len {
        let mut d = top_int[i] as i16 - bot_int[i] as i16 - borrow;
        borrow = 0;
        if d < 0 {
            d += 10;
            borrow = 1;
        }
        out_int.push(d as u8);
    }
    out_int.reverse();
    let start = out_int
        .iter()
        .position(|&d| d != 0)
        .unwrap_or(out_int.len().saturating_sub(1));
    let out_int = out_int[start..].to_vec();

    let int_str: String = if out_int.is_empty() {
        "0".to_string()
    } else {
        out_int.iter().map(|&d| (b'0' + d) as char).collect()
    };
    let frac_str: String = out_frac.iter().map(|&d| (b'0' + d) as char).collect();
    let frac_trim = frac_str.trim_end_matches('0');
    let result = if frac_trim.is_empty() {
        int_str
    } else {
        format!("{}.{}", int_str, frac_trim)
    };
    normalize_decimal_number_string(&result)
}

fn compare_decimal_parts(int_a: &[u8], frac_a: &[u8], int_b: &[u8], frac_b: &[u8]) -> i32 {
    let len_a = int_a.len();
    let len_b = int_b.len();
    if len_a != len_b {
        return (len_a as i32) - (len_b as i32);
    }
    for i in (0..len_a).rev() {
        if int_a[i] != int_b[i] {
            return int_a[i] as i32 - int_b[i] as i32;
        }
    }
    for i in 0..frac_a.len().max(frac_b.len()) {
        let da = match frac_a.get(i) {
            Some(&d) => d,
            None => 0,
        };
        let db = match frac_b.get(i) {
            Some(&d) => d,
            None => 0,
        };
        if da != db {
            return da as i32 - db as i32;
        }
    }
    0
}

/// Multiplies two non-negative decimal strings and returns a normalized product.
pub fn mul_decimal_str_and_normalize(a: &str, b: &str) -> String {
    let (int_a, frac_a) = parse_decimal_parts(a);
    let (int_b, frac_b) = parse_decimal_parts(b);
    let frac_places = frac_a.len() + frac_b.len();
    let digits_a: Vec<u8> = int_a
        .iter()
        .cloned()
        .chain(frac_a.iter().cloned())
        .collect();
    let digits_b: Vec<u8> = int_b
        .iter()
        .cloned()
        .chain(frac_b.iter().cloned())
        .collect();
    let len_a = digits_a.len();
    let len_b = digits_b.len();
    let mut product = vec![0u32; len_a + len_b];
    for (i, &da) in digits_a.iter().enumerate() {
        for (j, &db) in digits_b.iter().enumerate() {
            let place = (len_a - 1 - i) + (len_b - 1 - j);
            product[place] += da as u32 * db as u32;
        }
    }
    let mut carry = 0u32;
    for p in product.iter_mut() {
        *p += carry;
        carry = *p / 10;
        *p %= 10;
    }
    while carry > 0 {
        product.push(carry % 10);
        carry /= 10;
    }
    let total_len = product.len();
    let int_part: String = if frac_places >= total_len {
        "0".to_string()
    } else {
        product[frac_places..]
            .iter()
            .rev()
            .map(|&d| (b'0' + d as u8) as char)
            .collect::<String>()
            .trim_start_matches('0')
            .to_string()
    };
    let frac_part: String = if frac_places == 0 {
        String::new()
    } else {
        product[..frac_places.min(total_len)]
            .iter()
            .rev()
            .map(|&d| (b'0' + d as u8) as char)
            .collect::<String>()
            .trim_end_matches('0')
            .to_string()
    };
    let int_str = if int_part.is_empty() { "0" } else { &int_part };
    let result = if frac_part.is_empty() {
        int_str.to_string()
    } else {
        format!("{}.{}", int_str, frac_part)
    };
    normalize_decimal_number_string(&result)
}

/// Computes the Euclidean remainder on signed integer decimal strings.
///
/// The result is always non-negative and strictly smaller than the absolute
/// value of a non-zero divisor. For example, `-7 % 3 = 2`.
pub fn mod_decimal_str_and_normalize(a: &str, b: &str) -> String {
    let normalized_a = normalize_decimal_number_string(a);
    let normalized_b = normalize_decimal_number_string(b);
    let (a_is_negative, a_magnitude) = split_sign_and_magnitude(&normalized_a);
    let (_, b_magnitude) = split_sign_and_magnitude(&normalized_b);
    let remainder = mod_nonnegative_decimal_str_and_normalize(&a_magnitude, &b_magnitude);

    if a_is_negative && remainder != "0" {
        sub_decimal_str_and_normalize(&b_magnitude, &remainder)
    } else {
        remainder
    }
}

/// Computes the Euclidean quotient on signed integer decimal strings.
///
/// Together with [`mod_decimal_str_and_normalize`], this satisfies
/// `a = b * quot(a, b) + a % b` for a non-zero divisor. The public `quot`
/// object further restricts `b` to a positive natural.
pub fn quot_decimal_str_and_normalize(a: &str, b: &str) -> String {
    let normalized_a = normalize_decimal_number_string(a);
    let normalized_b = normalize_decimal_number_string(b);
    let (a_is_negative, a_magnitude) = split_sign_and_magnitude(&normalized_a);
    let (_, b_magnitude) = split_sign_and_magnitude(&normalized_b);
    let quotient = quot_nonnegative_decimal_str_and_normalize(&a_magnitude, &b_magnitude);
    let remainder = mod_nonnegative_decimal_str_and_normalize(&a_magnitude, &b_magnitude);

    if !a_is_negative || quotient == "0" && remainder == "0" {
        quotient
    } else if remainder == "0" {
        format!("-{quotient}")
    } else {
        format!("-{}", add_decimal_str_and_normalize(&quotient, "1"))
    }
}

fn quot_nonnegative_decimal_str_and_normalize(a: &str, b: &str) -> String {
    let (int_a, _) = parse_decimal_parts(a);
    let (int_b, _) = parse_decimal_parts(b);
    let a_digits = trim_leading_zeros(&int_a);
    let b_digits = trim_leading_zeros(&int_b);
    if a_digits.is_empty() || b_digits.is_empty() || (b_digits.len() == 1 && b_digits[0] == 0) {
        return "0".to_string();
    }

    let mut current: Vec<u8> = vec![];
    let mut quotient_digits = Vec::with_capacity(a_digits.len());
    for &digit in &a_digits {
        current.push(digit);
        current = trim_leading_zeros(&current);
        let mut quotient_digit = 9u8;
        loop {
            let product = mul_digit(&b_digits, quotient_digit);
            if compare_digits(&current, &product) != std::cmp::Ordering::Less {
                current = sub_digits(&current, &product);
                quotient_digits.push(quotient_digit);
                break;
            }
            quotient_digit -= 1;
        }
    }
    normalize_decimal_number_string(&digits_to_string(&trim_leading_zeros(&quotient_digits)))
}

fn mod_nonnegative_decimal_str_and_normalize(a: &str, b: &str) -> String {
    let (int_a, _) = parse_decimal_parts(a);
    let (int_b, _) = parse_decimal_parts(b);
    let a_digits = trim_leading_zeros(&int_a);
    let b_digits = trim_leading_zeros(&int_b);
    if a_digits.is_empty() {
        return "0".to_string();
    }
    if b_digits.is_empty() || (b_digits.len() == 1 && b_digits[0] == 0) {
        return "0".to_string();
    }
    if compare_digits(&a_digits, &b_digits) == std::cmp::Ordering::Less {
        return digits_to_string(&a_digits);
    }
    let mut current: Vec<u8> = vec![];
    for &da in &a_digits {
        current.push(da);
        current = trim_leading_zeros(&current);
        let mut d = 9u8;
        loop {
            let product = mul_digit(&b_digits, d);
            if compare_digits(&current, &product) != std::cmp::Ordering::Less {
                current = sub_digits(&current, &product);
                break;
            }
            if d == 0 {
                break;
            }
            d -= 1;
        }
    }
    normalize_decimal_number_string(&digits_to_string(&current))
}

const POW_DECIMAL_MAX_NORMALIZED_LENGTH: usize = 100;

// Non-negative integer exponent only; fractional exp => None (no exact decimal fold).
pub fn pow_decimal_str_and_normalize(base: &str, exp: &str) -> Option<String> {
    let n = parse_nonnegative_integer_exponent_for_pow(exp)?;
    if n == 0 {
        return Some("1".to_string());
    }

    let normalized_base = normalize_decimal_number_string(base);
    if normalized_base == "0" {
        return Some("0".to_string());
    }
    if normalized_base == "1" {
        return Some("1".to_string());
    }
    if normalized_base == "-1" {
        return if n % 2 == 0 {
            Some("1".to_string())
        } else {
            Some("-1".to_string())
        };
    }
    if pow_decimal_size_budget_exceeded(&normalized_base, n) {
        return None;
    }

    let mut acc = "1".to_string();
    let mut b = normalized_base;
    let mut e = n;
    while e > 0 {
        if e % 2 == 1 {
            acc = mul_signed_decimal_str(&acc, &b);
            if normalized_decimal_string_exceeds_pow_budget(&acc) {
                return None;
            }
        }
        e /= 2;
        if e > 0 {
            b = mul_signed_decimal_str(&b, &b);
            if normalized_decimal_string_exceeds_pow_budget(&b) {
                return None;
            }
        }
    }
    Some(normalize_decimal_number_string(&acc))
}

fn parse_nonnegative_integer_exponent_for_pow(exp: &str) -> Option<usize> {
    if exp.trim().starts_with('-') {
        return None;
    }
    let (exp_int, exp_frac) = parse_decimal_parts(exp);
    if exp_frac.iter().any(|&d| d != 0) {
        return None;
    }
    let mut n = 0usize;
    for &d in &exp_int {
        n = n.checked_mul(10)?.checked_add(d as usize)?;
    }
    Some(n)
}

fn pow_decimal_size_budget_exceeded(base: &str, exponent: usize) -> bool {
    if let Some(estimated_digits) = estimated_integer_power_digit_count(base, exponent) {
        return estimated_digits > POW_DECIMAL_MAX_NORMALIZED_LENGTH;
    }

    let magnitude = base.trim().strip_prefix('-').unwrap_or(base.trim());
    let (_, frac_str) = magnitude.split_once('.').unwrap_or((magnitude, ""));
    let significant_frac_digits = frac_str.trim_end_matches('0').len();
    match significant_frac_digits.checked_mul(exponent) {
        Some(digits) => digits > POW_DECIMAL_MAX_NORMALIZED_LENGTH,
        None => true,
    }
}

fn estimated_integer_power_digit_count(base: &str, exponent: usize) -> Option<usize> {
    let magnitude = base.trim().strip_prefix('-').unwrap_or(base.trim());
    if magnitude.contains('.') {
        return None;
    }

    let digits = magnitude.trim_start_matches('0');
    if digits.is_empty() {
        return Some(1);
    }

    let prefix_len = digits.len().min(16);
    let prefix = digits[..prefix_len].parse::<f64>().ok()?;
    let log10_base = prefix.log10() + (digits.len() - prefix_len) as f64;
    let estimated = (log10_base * exponent as f64).floor() + 1.0;
    if !estimated.is_finite() || estimated > usize::MAX as f64 {
        return Some(usize::MAX);
    }
    Some(estimated as usize)
}

fn normalized_decimal_string_exceeds_pow_budget(value: &str) -> bool {
    let magnitude = value.trim().strip_prefix('-').unwrap_or(value.trim());
    let normalized_len = magnitude.chars().filter(|c| *c != '.').count();
    normalized_len > POW_DECIMAL_MAX_NORMALIZED_LENGTH
}

fn trim_leading_zeros(d: &[u8]) -> Vec<u8> {
    let start = d.iter().position(|&x| x != 0).unwrap_or(d.len());
    d[start..].to_vec()
}

/// Converts big-endian digits into a decimal string.
fn digits_to_string(d: &[u8]) -> String {
    let t = trim_leading_zeros(d);
    if t.is_empty() {
        return "0".to_string();
    }
    t.iter().map(|&x| (b'0' + x) as char).collect()
}

/// Multiplies big-endian digits by one digit.
fn mul_digit(b: &[u8], d: u8) -> Vec<u8> {
    if d == 0 {
        return vec![0];
    }
    let mut b = b.to_vec();
    b.reverse();
    let mut carry = 0u16;
    for x in b.iter_mut() {
        let p = *x as u16 * d as u16 + carry;
        *x = (p % 10) as u8;
        carry = p / 10;
    }
    while carry > 0 {
        b.push((carry % 10) as u8);
        carry /= 10;
    }
    b.reverse();
    trim_leading_zeros(&b)
}

/// Compares two big-endian integer digit sequences.
fn compare_digits(a: &[u8], b: &[u8]) -> std::cmp::Ordering {
    let a = trim_leading_zeros(a);
    let b = trim_leading_zeros(b);
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for (x, y) in a.iter().zip(b.iter()) {
        if x != y {
            return x.cmp(y);
        }
    }
    std::cmp::Ordering::Equal
}

/// Subtracts big-endian digit sequences, assuming `a >= b`.
fn sub_digits(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut a = a.to_vec();
    let mut b = b.to_vec();
    let len = a.len().max(b.len());
    a.reverse();
    b.reverse();
    a.resize(len, 0);
    b.resize(len, 0);
    let mut borrow: i16 = 0;
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        let mut d = a[i] as i16 - b[i] as i16 - borrow;
        borrow = 0;
        if d < 0 {
            d += 10;
            borrow = 1;
        }
        out.push(d as u8);
    }
    out.reverse();
    trim_leading_zeros(&out)
}

/// Normalizes signs, zero forms, and trailing decimal zeros.
pub fn normalize_decimal_number_string(s: &str) -> String {
    let s = s.trim();
    if s.is_empty() {
        return "0".to_string();
    }
    let minus_count = s.chars().take_while(|&c| c == '-').count();
    let rest = s[minus_count..].trim();
    let negative = (minus_count % 2) == 1;

    let magnitude = if rest.contains('.') {
        let (int_str, frac_str) = rest.split_once('.').unwrap_or((rest, ""));
        let frac_trimmed = frac_str.trim_end_matches('0');
        let int_trimmed = int_str.trim_start_matches('0');
        let int_part = if int_trimmed.is_empty() || int_trimmed == "." {
            "0"
        } else {
            int_trimmed
        };
        if frac_trimmed.is_empty() {
            int_part.to_string()
        } else {
            format!("{}.{}", int_part, frac_trimmed)
        }
    } else {
        let t = rest.trim_start_matches('0');
        if t.is_empty() { "0" } else { t }.to_string()
    };

    let is_zero = magnitude == "0"
        || (magnitude.starts_with("0.") && magnitude[2..].chars().all(|c| c == '0'));
    if is_zero {
        "0".to_string()
    } else if negative {
        format!("-{}", magnitude)
    } else {
        magnitude
    }
}

/// Parses a decimal string into integer and fractional digit vectors.
fn parse_decimal_parts(s: &str) -> (Vec<u8>, Vec<u8>) {
    let s = s.trim();
    let (int_str, frac_str) = match s.find('.') {
        Some(i) => (&s[..i], &s[i + 1..]),
        None => (s, ""),
    };
    let int_digits: Vec<u8> = if int_str.is_empty() || int_str == "-" {
        vec![0]
    } else {
        int_str
            .chars()
            .filter(|c| c.is_ascii_digit())
            .map(|c| c as u8 - b'0')
            .collect()
    };
    let frac_digits: Vec<u8> = frac_str
        .chars()
        .filter(|c| c.is_ascii_digit())
        .map(|c| c as u8 - b'0')
        .collect();
    let int_digits = if int_digits.is_empty() {
        vec![0]
    } else {
        int_digits
    };
    (int_digits, frac_digits)
}

#[cfg(test)]
#[path = "../../tests/unit/algebraic_normalization/decimal_arithmetic/tests.rs"]
mod tests;
