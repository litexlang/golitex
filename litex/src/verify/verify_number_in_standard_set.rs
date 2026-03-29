//! Decides whether a decimal Number belongs to a standard number set (N, N_pos, Z, Z_neg, Z_nz, Q, R, etc.).

use crate::prelude::*;

/// Parses number string into sign and digit parts. Handles "-1.00", "0", "0.5".
fn parse_number_parts(value: &str) -> (bool, Vec<u8>, Vec<u8>) {
    let s = value.trim();
    let (negative, magnitude) = if s.starts_with('-') {
        (true, s[1..].trim())
    } else {
        (false, s)
    };
    let (int_digits, frac_digits) = parse_decimal_parts(magnitude);
    (negative, int_digits, frac_digits)
}

/// Splits magnitude string into (integer part digits, fractional part digits). No sign.
fn parse_decimal_parts(s: &str) -> (Vec<u8>, Vec<u8>) {
    let (int_str, frac_str) = match s.find('.') {
        Some(i) => (&s[..i], &s[i + 1..]),
        None => (s, ""),
    };
    let int_digits: Vec<u8> = if int_str.is_empty() {
        vec![0]
    } else {
        int_str
            .chars()
            .filter(|c| c.is_ascii_digit())
            .map(|c| c as u8 - b'0')
            .collect()
    };
    let int_digits = if int_digits.is_empty() {
        vec![0]
    } else {
        int_digits
    };
    let frac_digits: Vec<u8> = frac_str
        .chars()
        .filter(|c| c.is_ascii_digit())
        .map(|c| c as u8 - b'0')
        .collect();
    (int_digits, frac_digits)
}

fn digits_all_zero(digits: &[u8]) -> bool {
    digits.iter().all(|&d| d == 0)
}

/// True if the number is a whole number (no fractional part or fractional part all zeros, e.g. -1.00, 2.0).
pub fn is_integer_after_simplification(number: &Number) -> bool {
    let (_, _, frac_digits) = parse_number_parts(&number.normalized_value);
    frac_digits.is_empty() || digits_all_zero(&frac_digits)
}

fn number_is_zero(number: &Number) -> bool {
    let (_, int_digits, frac_digits) = parse_number_parts(&number.normalized_value);
    digits_all_zero(&int_digits) && (frac_digits.is_empty() || digits_all_zero(&frac_digits))
}

fn number_is_positive(number: &Number) -> bool {
    let (negative, int_digits, frac_digits) = parse_number_parts(&number.normalized_value);
    let zero =
        digits_all_zero(&int_digits) && (frac_digits.is_empty() || digits_all_zero(&frac_digits));
    !negative && !zero
}

fn number_is_negative(number: &Number) -> bool {
    let (negative, int_digits, frac_digits) = parse_number_parts(&number.normalized_value);
    let zero =
        digits_all_zero(&int_digits) && (frac_digits.is_empty() || digits_all_zero(&frac_digits));
    negative && !zero
}

fn number_is_nonzero(number: &Number) -> bool {
    !number_is_zero(number)
}

// --- Z (integers) ---
pub fn number_is_in_z(number: &Number) -> bool {
    is_integer_after_simplification(number)
}

// --- N (naturals: 0, 1, 2, ...) ---
pub fn number_is_in_n(number: &Number) -> bool {
    number_is_in_z(number) && !number_is_negative(number)
}

// --- N_pos (positive naturals: 1, 2, 3, ...) ---
pub fn number_is_in_n_pos(number: &Number) -> bool {
    number_is_in_z(number) && number_is_positive(number)
}

// --- Z_neg (negative integers) ---
pub fn number_is_in_z_neg(number: &Number) -> bool {
    number_is_in_z(number) && number_is_negative(number)
}

// --- Z_nz (non-zero integers) ---
pub fn number_is_in_z_nz(number: &Number) -> bool {
    number_is_in_z(number) && number_is_nonzero(number)
}

// --- Q_pos, R_pos (positive rationals/reals) ---
pub fn number_is_in_q_pos(number: &Number) -> bool {
    number_is_positive(number)
}

pub fn number_is_in_r_pos(number: &Number) -> bool {
    number_is_positive(number)
}

// --- Q_neg, R_neg ---
pub fn number_is_in_q_neg(number: &Number) -> bool {
    number_is_negative(number)
}

pub fn number_is_in_r_neg(number: &Number) -> bool {
    number_is_negative(number)
}

// --- Q_nz, R_nz (non-zero) ---
pub fn number_is_in_q_nz(number: &Number) -> bool {
    number_is_nonzero(number)
}

pub fn number_is_in_r_nz(number: &Number) -> bool {
    number_is_nonzero(number)
}
