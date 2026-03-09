use crate::errors::ArithmeticError;
use crate::obj::Obj;
use crate::obj::{Add, Div, Mod, Mul, Number, Pow, Sub};

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
    let int_digits = if int_digits.is_empty() { vec![0] } else { int_digits };
    (int_digits, frac_digits)
}

/// 竖式加法：两个表示非负数的数字串（可含小数点），返回和的字符串
pub fn add_decimal_str(a: &str, b: &str) -> String {
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
    if frac_str.is_empty() || out_frac.iter().all(|&d| d == 0) {
        int_str
    } else {
        format!("{}.{}", int_str, frac_str.trim_end_matches('0'))
    }
}

/// 竖式减法：a - b，若 a >= b 返回非负结果字符串，否则返回 "-" + (b - a) 的字符串
pub fn sub_decimal_str(a: &str, b: &str) -> String {
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
        let mut prefix = String::from("-");
        prefix.push_str(&sub_decimal_str(b, a));
        return prefix;
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
    let start = out_int.iter().position(|&d| d != 0).unwrap_or(out_int.len().saturating_sub(1));
    let out_int = out_int[start..].to_vec();

    let int_str: String = if out_int.is_empty() {
        "0".to_string()
    } else {
        out_int.iter().map(|&d| (b'0' + d) as char).collect()
    };
    let frac_str: String = out_frac.iter().map(|&d| (b'0' + d) as char).collect();
    let frac_trim = frac_str.trim_end_matches('0');
    if frac_trim.is_empty() {
        int_str
    } else {
        format!("{}.{}", int_str, frac_trim)
    }
}

fn compare_decimal_parts(
    int_a: &[u8],
    frac_a: &[u8],
    int_b: &[u8],
    frac_b: &[u8],
) -> i32 {
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
        let da = frac_a.get(i).copied().unwrap_or(0);
        let db = frac_b.get(i).copied().unwrap_or(0);
        if da != db {
            return da as i32 - db as i32;
        }
    }
    0
}

/// 竖式乘法：两个非负数字串，返回积的字符串（product[0]=个位，即最低位）
fn mul_decimal_str(a: &str, b: &str) -> String {
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
    if frac_part.is_empty() {
        int_str.to_string()
    } else {
        format!("{}.{}", int_str, frac_part)
    }
}

/// 将十进制数字串转为“缩放整数”的各位数字（无小数点），及小数位数。例如 "12.34" -> (vec![1,2,3,4], 2)
fn to_scaled_digits(s: &str) -> (Vec<u8>, usize) {
    let (int_d, frac_d) = parse_decimal_parts(s);
    let frac_len = frac_d.len();
    let digits: Vec<u8> = int_d
        .iter()
        .cloned()
        .chain(frac_d.iter().cloned())
        .collect();
    let digits = trim_leading_zeros(&digits);
    (if digits.is_empty() { vec![0] } else { digits }, frac_len)
}

fn trim_leading_zeros(d: &[u8]) -> Vec<u8> {
    let start = d.iter().position(|&x| x != 0).unwrap_or(d.len());
    d[start..].to_vec()
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

/// 竖式取余：a mod b = a - floor(a/b)*b，返回余数字符串。用 scaled 整数 (Q,R) 则 a mod b = R/10^(scale_a+scale_b)
fn mod_decimal_str(a: &str, b: &str) -> String {
    panic!("NOT IMPLEMENTED YET");
}

/// 仅支持非负整数指数：base^exp，exp 必须为整数（如 "3" 或 "0"），返回字符串
fn pow_decimal_str_int_exp(base: &str, exp: &str) -> Result<String, ArithmeticError> {
    let (exp_int, exp_frac) = parse_decimal_parts(exp);
    if exp_frac.iter().any(|&d| d != 0) {
        return Err(ArithmeticError::new("幂运算仅支持整数指数"));
    }
    let mut n = 0usize;
    for &d in &exp_int {
        n = n.saturating_mul(10).saturating_add(d as usize);
    }
    if n == 0 {
        return Ok("1".to_string());
    }
    let mut acc = "1".to_string();
    let mut b = base.to_string();
    let mut e = n;
    while e > 0 {
        if e % 2 == 1 {
            acc = mul_decimal_str(&acc, &b);
        }
        b = mul_decimal_str(&b, &b);
        e /= 2;
    }
    Ok(acc)
}

/// 仅当两边都是 Number 时取数值串，否则报错
fn require_two_number_str(
    l: &Obj,
    r: &Obj,
    op: &str,
) -> Result<(String, String), ArithmeticError> {
    match (l, r) {
        (Obj::Number(ln), Obj::Number(rn)) => Ok((ln.value.clone(), rn.value.clone())),
        _ => Err(ArithmeticError::new(&format!(
            "{} 要求两边均为数字（字符串形式）",
            op
        ))),
    }
}

impl Obj {
    pub fn calculate(&self) -> Result<Obj, ArithmeticError> {
        match self {
            Obj::Number(n) => Ok(Obj::Number(Number {
                value: n.value.clone(),
            })),
            Obj::Add(a) => a.calculate(),
            Obj::Sub(s) => s.calculate(),
            Obj::Mul(m) => m.calculate(),
            Obj::Mod(m) => m.calculate(),
            Obj::Pow(p) => p.calculate(),
            _ => Err(ArithmeticError::new("非算术表达式，无法 calculate")),
        }
    }
}

impl Add {
    pub fn calculate(&self) -> Result<Obj, ArithmeticError> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticError::new("非算术表达式，无法 calculate"));
        }
        let l = self.left.calculate()?;
        let r = self.right.calculate()?;
        let (lv, rv) = require_two_number_str(&l, &r, "加法")?;
        Ok(Obj::Number(Number {
            value: add_decimal_str(&lv, &rv),
        }))
    }
}

impl Sub {
    pub fn calculate(&self) -> Result<Obj, ArithmeticError> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticError::new("非算术表达式，无法 calculate"));
        }
        let l = self.left.calculate()?;
        let r = self.right.calculate()?;
        let (lv, rv) = require_two_number_str(&l, &r, "减法")?;
        Ok(Obj::Number(Number {
            value: sub_decimal_str(&lv, &rv),
        }))
    }
}

impl Mul {
    pub fn calculate(&self) -> Result<Obj, ArithmeticError> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticError::new("非算术表达式，无法 calculate"));
        }
        let l = self.left.calculate()?;
        let r = self.right.calculate()?;
        let (lv, rv) = require_two_number_str(&l, &r, "乘法")?;
        Ok(Obj::Number(Number {
            value: mul_decimal_str(&lv, &rv),
        }))
    }
}

impl Mod {
    pub fn calculate(&self) -> Result<Obj, ArithmeticError> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticError::new("非算术表达式，无法 calculate"));
        }
        let l = self.left.calculate()?;
        let r = self.right.calculate()?;
        let (lv, rv) = require_two_number_str(&l, &r, "取余")?;
        Ok(Obj::Number(Number {
            value: mod_decimal_str(&lv, &rv),
        }))
    }
}

impl Pow {
    pub fn calculate(&self) -> Result<Obj, ArithmeticError> {
        if !self.is_arithmetic_expr {
            return Err(ArithmeticError::new("非算术表达式，无法 calculate"));
        }
        let base = self.base.calculate()?;
        let exp = self.exponent.calculate()?;
        let (base_s, exp_s) = require_two_number_str(&base, &exp, "幂运算")?;
        let value = pow_decimal_str_int_exp(&base_s, &exp_s)?;
        Ok(Obj::Number(Number { value }))
    }
}
