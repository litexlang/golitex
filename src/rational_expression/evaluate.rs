use crate::prelude::*;
use crate::rational_expression::evaluate_div::safe_div;

impl Obj {
    pub fn evaluate_to_normalized_decimal_number(&self) -> Option<Number> {
        let result = match self {
            Obj::Number(number) => Some(number.clone()),
            Obj::Add(add) => {
                let left_number = add.left.evaluate_to_normalized_decimal_number();
                let right_number = add.right.evaluate_to_normalized_decimal_number();
                if let (Some(left_number), Some(right_number)) = (left_number, right_number) {
                    let a = &left_number.normalized_value;
                    let b = &right_number.normalized_value;
                    let sum = if normalized_decimal_str_is_non_negative(a)
                        && normalized_decimal_str_is_non_negative(b)
                    {
                        // `add_decimal_str_and_normalize` 仅适用于两操作数非负（见函数注释）
                        add_decimal_str_and_normalize(a, b)
                    } else {
                        add_signed_decimal_str(a, b)
                    };
                    Some(Number::new(sum))
                } else {
                    None
                }
            }
            Obj::Sub(sub) => {
                let left_number = sub.left.evaluate_to_normalized_decimal_number();
                let right_number = sub.right.evaluate_to_normalized_decimal_number();
                if let (Some(left_number), Some(right_number)) = (left_number, right_number) {
                    let a = &left_number.normalized_value;
                    let b = &right_number.normalized_value;
                    let diff = if normalized_decimal_str_is_non_negative(a)
                        && normalized_decimal_str_is_non_negative(b)
                    {
                        // `sub_decimal_str_and_normalize` 的竖式比较同样按非负量设计
                        sub_decimal_str_and_normalize(a, b)
                    } else {
                        sub_signed_decimal_str(a, b)
                    };
                    Some(Number::new(diff))
                } else {
                    None
                }
            }
            Obj::Mul(mul) => {
                let left_number = mul.left.evaluate_to_normalized_decimal_number();
                let right_number = mul.right.evaluate_to_normalized_decimal_number();
                if let (Some(left_number), Some(right_number)) = (left_number, right_number) {
                    Some(Number::new(mul_signed_decimal_str(
                        &left_number.normalized_value,
                        &right_number.normalized_value,
                    )))
                } else {
                    None
                }
            }
            Obj::Mod(mod_obj) => {
                let left_number = mod_obj.left.evaluate_to_normalized_decimal_number();
                let right_number = mod_obj.right.evaluate_to_normalized_decimal_number();
                if let (Some(left_number), Some(right_number)) = (left_number, right_number) {
                    Some(Number::new(mod_decimal_str_and_normalize(
                        &left_number.normalized_value,
                        &right_number.normalized_value,
                    )))
                } else {
                    None
                }
            }
            Obj::Pow(pow_obj) => {
                let base_number = pow_obj.base.evaluate_to_normalized_decimal_number();
                let exponent_number = pow_obj.exponent.evaluate_to_normalized_decimal_number();
                if let (Some(base_number), Some(exponent_number)) = (base_number, exponent_number) {
                    Some(Number::new(pow_decimal_str_and_normalize(
                        &base_number.normalized_value,
                        &exponent_number.normalized_value,
                    )))
                } else {
                    None
                }
            }
            Obj::Div(div) => {
                let left_number = div.left.evaluate_to_normalized_decimal_number();
                let right_number = div.right.evaluate_to_normalized_decimal_number();
                if let (Some(left_number), Some(right_number)) = (left_number, right_number) {
                    let exact_quotient_string = safe_div(
                        &left_number.normalized_value,
                        &right_number.normalized_value,
                    );

                    if let Some(exact_quotient_string) = exact_quotient_string {
                        Some(Number::new(exact_quotient_string))
                    } else {
                        None
                    }
                } else {
                    return None;
                }
            }
            Obj::CartDim(cart_dim) => match &*cart_dim.set {
                Obj::Cart(cart) => Some(Number::new(cart.args.len().to_string())),
                _ => None,
            },
            Obj::TupleDim(tuple_dim) => match &*tuple_dim.arg {
                Obj::Tuple(tuple) => Some(Number::new(tuple.args.len().to_string())),
                _ => None,
            },
            Obj::Count(count) => match &*count.set {
                Obj::ListSet(list_set) => Some(Number::new(list_set.list.len().to_string())),
                _ => None,
            },
            _ => None,
        };

        match result {
            Some(number) => Some(number),
            None => None,
        }
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

/// 规范化后的十进制串是否表示非负数（无 `-` 前缀；`-0` 若已规范为 `0` 亦视为非负）。
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

/// 带符号加法 a + b（系数合并用；`add_decimal_str_and_normalize` 仅适用于非负操作数）
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

/// 带符号减法 a - b
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

/// 竖式加法：两个表示非负数的数字串（可含小数点），返回和的字符串
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

/// 竖式减法：a - b，若 a >= b 返回非负结果字符串，否则返回 "-" + (b - a) 的字符串
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

/// 竖式乘法：两个非负数字串，返回积的字符串（product[0]=个位，即最低位）
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

/// 竖式取余：a mod b，返回余数字符串。约定：b 仅为非零纯整数（字符串），a 取整数部分参与运算。
pub fn mod_decimal_str_and_normalize(a: &str, b: &str) -> String {
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

/// 仅支持非负整数指数：base^exp，exp 必须为整数（如 "3" 或 "0"），返回字符串
pub fn pow_decimal_str_and_normalize(base: &str, exp: &str) -> String {
    let (exp_int, exp_frac) = parse_decimal_parts(exp);
    if exp_frac.iter().any(|&d| d != 0) {
        unreachable!("幂运算仅支持整数指数");
    }
    let mut n = 0usize;
    for &d in &exp_int {
        n = n.saturating_mul(10).saturating_add(d as usize);
    }
    if n == 0 {
        return "1".to_string();
    }
    let mut acc = "1".to_string();
    let mut b = base.to_string();
    let mut e = n;
    while e > 0 {
        if e % 2 == 1 {
            acc = mul_decimal_str_and_normalize(&acc, &b);
        }
        b = mul_decimal_str_and_normalize(&b, &b);
        e /= 2;
    }
    normalize_decimal_number_string(&acc)
}

fn trim_leading_zeros(d: &[u8]) -> Vec<u8> {
    let start = d.iter().position(|&x| x != 0).unwrap_or(d.len());
    d[start..].to_vec()
}

/// 数字序列转字符串（高位在前）
fn digits_to_string(d: &[u8]) -> String {
    let t = trim_leading_zeros(d);
    if t.is_empty() {
        return "0".to_string();
    }
    t.iter().map(|&x| (b'0' + x) as char).collect()
}

/// 大数乘一位数：b * d，0 <= d <= 9，返回各位（高位在前）
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

/// 比较两个“整数”数字序列（高位在前）
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

/// 大数减法：要求 a >= b，返回 a - b 的各位（高位在前）
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

/// 化简结果：多个负号合并（---1.1 -> -1.1）、0.0或者-0 写成 0、小数尾零去掉（1.000 -> 1）
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

/// 解析数字串为 (整数部分数字, 小数部分数字)，允许 "123.45"、"123"、".5"、"0.5"
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
