use std::fmt;
use crate::keywords::{COMMA,   LEFT_BRACE, LEFT_CURLY_BRACE, RIGHT_BRACE, RIGHT_CURLY_BRACE};

pub fn braced_vec_to_string<T: fmt::Display>(vec: &Vec<T>) -> String {
    format!("{}{}{}", LEFT_BRACE, vec_to_string_with_sep(vec, ", "), RIGHT_BRACE)
}

pub fn curly_braced_vec_to_string<T: fmt::Display>(vec: &Vec<T>) -> String {
    format!("{}{}{}", LEFT_CURLY_BRACE, vec_to_string_with_sep(vec, ", "), RIGHT_CURLY_BRACE)
}

pub fn vec_to_string_with_sep<T: fmt::Display>(vec: &Vec<T>, sep: &str) -> String {
    vec.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(sep)
}

pub fn braced_string<T: fmt::Display>(str: &T) -> String {
    format!("{}{}{}", LEFT_BRACE, str, RIGHT_BRACE)
}

pub fn braced_two_strings<T: fmt::Display>(str1: &T, str2: &T) -> String {
    format!("{}{}{} {}{}", LEFT_BRACE, str1, COMMA, str2, RIGHT_BRACE)
}

pub fn vec_pair_to_string<A: fmt::Display, B: fmt::Display>(left: &Vec<A>, right: &Vec<B>) -> String {
    if left.len() != right.len() {
        panic!("left and right must have the same length");
    }
    left.iter().zip(right.iter()).map(|(l, r)| format!("{} {}", l, r)).collect::<Vec<String>>().join(", ")
}

pub fn to_string_and_add_four_spaces_at_beginning_of_each_line<T: fmt::Display>(fact: &T, number_of_four_spaces: usize) -> String {
    fact.to_string().split("\n").map(|fact| format!("{}{}", "    ".repeat(number_of_four_spaces), fact)).collect::<Vec<String>>().join("\n")
}

pub fn curly_braced_vec_to_string_with_sep<T: fmt::Display>(vec: &Vec<T>, sep: &str) -> String {
    format!("{}{}{}", LEFT_CURLY_BRACE, vec_to_string_with_sep(vec, sep), RIGHT_CURLY_BRACE)
}

pub fn vec_to_string_join_by_comma<T: fmt::Display>(vec: &Vec<T>) -> String {
    vec.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
}

pub fn line_file_suffix(line_file_index: Option<(u16, usize)>) -> String {
    match line_file_index {
        Some((line, _)) => format!(" on line {}:", line),
        None => ":".to_string(),
    }
}

pub fn vec_to_string_add_four_spaces_at_beginning_of_each_line<T: fmt::Display>(vec: &Vec<T>, number_of_four_spaces: usize) -> String {
    to_string_and_add_four_spaces_at_beginning_of_each_line(&vec_to_string_with_sep(vec, "\n"), number_of_four_spaces)
}

pub fn add_four_spaces_at_beginning(str: &str, number_of_four_spaces: usize) -> String {
    format!("{}{}", "    ".repeat(number_of_four_spaces), str)
}

