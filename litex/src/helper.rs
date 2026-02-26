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

/// 两列不同类型（如 参数名 Vec<String> 与 参数类型 Vec<ParameterSet>）配对成 "a set, b nonempty_set" 形式
pub fn vec_pair_to_string<A: fmt::Display, B: fmt::Display>(left: &Vec<A>, right: &Vec<B>) -> String {
    if left.len() != right.len() {
        panic!("left and right must have the same length");
    }
    left.iter().zip(right.iter()).map(|(l, r)| format!("{} {}", l, r)).collect::<Vec<String>>().join(", ")
}

pub fn add_four_spaces_to_vec_at_beginning<A: fmt::Display>(facts: &Vec<A>, number_of_four_spaces: usize) -> String {
    facts.iter().map(|fact| format!("{}{}", "    ".repeat(number_of_four_spaces), fact)).collect::<Vec<String>>().join("\n")
}

pub fn add_four_spaces_to_str_at_beginning(facts: &str, number_of_four_spaces: usize) -> String {
    format!("{}{}", "    ".repeat(number_of_four_spaces), facts)
}

pub fn curly_braced_vec_to_string_with_sep<T: fmt::Display>(vec: &Vec<T>, sep: &str) -> String {
    format!("{}{}{}", LEFT_CURLY_BRACE, vec_to_string_with_sep(vec, sep), RIGHT_CURLY_BRACE)
}

pub fn str_with_line_file(s: &str, line: u32, file_index: usize) -> String {
    format!("{}\non line {}\nin file {}", s, line, file_index)
}