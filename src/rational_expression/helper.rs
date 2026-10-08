use crate::ast::obj::{Add, ArithmeticOperator, Div, Literal, Mul, Number, Obj, Sub};

/// True when the number spelling has no decimal point (e.g. `3`, not `3.0`).
pub fn is_number_string_literally_integer_without_dot(str: String) -> bool {
    !str.contains('.')
}

pub fn obj_key(obj: &Obj) -> String {
    obj.ir().display_string()
}

pub fn number_from_normalized(normalized_value: String) -> Number {
    Number::new(normalized_value)
}

impl Number {
    pub fn new(normalized_value: String) -> Self {
        Self {
            normalized_value: super::decimal_arithmetic::normalize_decimal_number_string(
                &normalized_value,
            ),
        }
    }
}

pub fn obj_from_number(number: Number) -> Obj {
    Obj::Literal(Literal::Number(number))
}

pub fn add_objs(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(left),
        right: Box::new(right),
    }))
}

pub fn sub_objs(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(left),
        right: Box::new(right),
    }))
}

pub fn mul_objs(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(left),
        right: Box::new(right),
    }))
}

pub fn div_objs(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(left),
        right: Box::new(right),
    }))
}

pub fn number_string_is_literal_integer_without_dot(value: &str) -> bool {
    is_number_string_literally_integer_without_dot(value.to_string())
}

pub fn count_closed_range_integer_endpoints(a: &Number, b: &Number) -> Option<Number> {
    let as_ = a.normalized_value.trim();
    let bs = b.normalized_value.trim();
    if !number_string_is_literal_integer_without_dot(as_)
        || !number_string_is_literal_integer_without_dot(bs)
    {
        return None;
    }
    let ai: i128 = as_.parse().ok()?;
    let bi: i128 = bs.parse().ok()?;
    if ai > bi {
        return Some(Number::new("0".to_string()));
    }
    let cnt = bi.checked_sub(ai)?.checked_add(1)?;
    Some(Number::new(cnt.to_string()))
}

pub fn count_half_open_range_integer_endpoints(a: &Number, b: &Number) -> Option<Number> {
    let as_ = a.normalized_value.trim();
    let bs = b.normalized_value.trim();
    if !number_string_is_literal_integer_without_dot(as_)
        || !number_string_is_literal_integer_without_dot(bs)
    {
        return None;
    }
    let ai: i128 = as_.parse().ok()?;
    let bi: i128 = bs.parse().ok()?;
    if bi <= ai {
        return Some(Number::new("0".to_string()));
    }
    let cnt = bi.checked_sub(ai)?;
    Some(Number::new(cnt.to_string()))
}
