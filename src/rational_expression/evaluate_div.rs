fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// 判断是否有限小数
fn is_finite(a: &str, b: &str) -> (bool, i128, i128) {
    fn parse(s: &str) -> (i128, i32) {
        if let Some(pos) = s.find('.') {
            let int = &s[..pos];
            let frac = &s[pos + 1..];
            let num = format!("{}{}", int, frac).parse::<i128>().unwrap();
            (num, frac.len() as i32)
        } else {
            (s.parse::<i128>().unwrap(), 0)
        }
    }

    let (a_num, a_dec) = parse(a);
    let (b_num, b_dec) = parse(b);

    let numerator = a_num * 10_i128.pow(b_dec as u32);
    let denominator = b_num * 10_i128.pow(a_dec as u32);

    let g = gcd(numerator, denominator);
    let mut d = denominator / g;

    while d % 2 == 0 {
        d /= 2;
    }
    while d % 5 == 0 {
        d /= 5;
    }

    (d == 1, numerator / g, denominator / g)
}

// 字符串长除法（保证会终止）；这里只处理非负整数，符号在外层单独处理。
fn divide(n: i128, d: i128) -> String {
    let mut result = String::new();

    // 整数部分
    result.push_str(&(n / d).to_string());
    let mut r = n % d;

    if r == 0 {
        return result;
    }

    result.push('.');

    while r != 0 {
        r *= 10;
        result.push(char::from(b'0' + (r / d) as u8));
        r %= d;
    }

    result
}

pub fn safe_div(a: &str, b: &str) -> Option<String> {
    let (ok, n, d) = is_finite(a, b);

    if !ok || d == 0 {
        return None;
    }

    let result_is_negative = (n < 0) ^ (d < 0);
    let quotient = divide(n.abs(), d.abs());
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
    }
}
