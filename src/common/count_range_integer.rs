use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::obj::Number;

/// Integer `closed_range(a, b)` has `max(0, b - a + 1)` points; non-integer endpoints yield `None`.
pub fn count_closed_range_integer_endpoints(a: &Number, b: &Number) -> Option<Number> {
    let as_ = a.normalized_value.trim();
    let bs = b.normalized_value.trim();
    if !is_number_string_literally_integer_without_dot(as_.to_string())
        || !is_number_string_literally_integer_without_dot(bs.to_string())
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

/// Integer `range(a, b)` is half-open `[a, b)`; size `max(0, b - a)` when `b > a`.
pub fn count_half_open_range_integer_endpoints(a: &Number, b: &Number) -> Option<Number> {
    let as_ = a.normalized_value.trim();
    let bs = b.normalized_value.trim();
    if !is_number_string_literally_integer_without_dot(as_.to_string())
        || !is_number_string_literally_integer_without_dot(bs.to_string())
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
