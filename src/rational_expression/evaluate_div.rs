fn gcd(a: i128, b: i128) -> Option<i128> {
    let mut a = a.checked_abs()?;
    let mut b = b.checked_abs()?;
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    Some(a)
}

// 判断是否有限小数
fn finite_reduced_fraction(a: &str, b: &str) -> Option<(i128, i128)> {
    fn parse(s: &str) -> Option<(i128, u32)> {
        if let Some(pos) = s.find('.') {
            let int = &s[..pos];
            let frac = &s[pos + 1..];
            let num = format!("{}{}", int, frac).parse::<i128>().ok()?;
            let decimal_places = u32::try_from(frac.len()).ok()?;
            Some((num, decimal_places))
        } else {
            Some((s.parse::<i128>().ok()?, 0))
        }
    }

    let (a_num, a_dec) = parse(a)?;
    let (b_num, b_dec) = parse(b)?;

    let numerator = a_num.checked_mul(10_i128.checked_pow(b_dec)?)?;
    let denominator = b_num.checked_mul(10_i128.checked_pow(a_dec)?)?;
    if denominator == 0 {
        return None;
    }

    let g = gcd(numerator, denominator)?;
    let reduced_numerator = numerator.checked_div(g)?;
    let reduced_denominator = denominator.checked_div(g)?;
    let mut d = reduced_denominator.checked_abs()?;

    while d % 2 == 0 {
        d /= 2;
    }
    while d % 5 == 0 {
        d /= 5;
    }

    if d == 1 {
        Some((reduced_numerator, reduced_denominator))
    } else {
        None
    }
}

// 字符串长除法（保证会终止）；这里只处理非负整数，符号在外层单独处理。
fn divide(n: i128, d: i128) -> Option<String> {
    let mut result = String::new();

    // 整数部分
    result.push_str(&(n / d).to_string());
    let mut r = n % d;

    if r == 0 {
        return Some(result);
    }

    result.push('.');

    while r != 0 {
        r = r.checked_mul(10)?;
        result.push(char::from(b'0' + (r / d) as u8));
        r %= d;
    }

    Some(result)
}

pub fn safe_div(a: &str, b: &str) -> Option<String> {
    let (n, d) = finite_reduced_fraction(a, b)?;

    let result_is_negative = (n < 0) ^ (d < 0);
    let quotient = divide(n.checked_abs()?, d.checked_abs()?)?;
    if result_is_negative && quotient != "0" {
        Some(format!("-{}", quotient))
    } else {
        Some(quotient)
    }
}

#[cfg(test)]
mod tests {
    use super::safe_div;

    #[test]
    fn safe_div_handles_negative_finite_decimal() {
        assert_eq!(safe_div("4", "5"), Some("0.8".to_string()));
        assert_eq!(safe_div("-4", "5"), Some("-0.8".to_string()));
        assert_eq!(safe_div("4", "-5"), Some("-0.8".to_string()));
        assert_eq!(safe_div("-4", "-5"), Some("0.8".to_string()));
    }

    #[test]
    fn safe_div_returns_none_for_oversized_numbers() {
        assert_eq!(
            safe_div("1", "99999999999999999999999999999999999999999"),
            None
        );
        assert_eq!(
            safe_div("1", "0.000000000000000000000000000000000000001"),
            None
        );
    }
}
