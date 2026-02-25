use std::fmt;
use crate::consts::{COMMA, LEFT_BRACE, LEFT_CURLY_BRACE, RIGHT_BRACE, RIGHT_CURLY_BRACE};

pub fn braced_vec_to_string<T: fmt::Display>(vec: &Vec<T>) -> String {
    format!("{}{}{}", LEFT_BRACE, vec_to_string_with_sep(vec, ", "), RIGHT_BRACE)
}

pub fn curly_braced_vec_to_string<T: fmt::Display>(vec: &Vec<T>) -> String {
    format!("{}{}{}", LEFT_CURLY_BRACE, vec_to_string_with_sep(vec, ", "), RIGHT_CURLY_BRACE)
}

/// 使用自定义分隔符
fn vec_to_string_with_sep<T: fmt::Display>(vec: &Vec<T>, sep: &str) -> String {
    vec.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(sep)
}

pub fn braced_string<T: fmt::Display>(str: &T) -> String {
    format!("{}{}{}", LEFT_BRACE, str, RIGHT_BRACE)
}

pub fn braced_two_strings<T: fmt::Display>(str1: &T, str2: &T) -> String {
    format!("{}{}{} {}{}", LEFT_BRACE, str1, COMMA, str2, RIGHT_BRACE)
}