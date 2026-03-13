use std::collections::HashSet;
use std::fmt::{self};
use std::hash::Hash;
use super::keywords::{LEFT_BRACE, LEFT_CURLY_BRACE, RIGHT_BRACE, RIGHT_CURLY_BRACE, DOT_AKA_FIELD_ACCESS_SIGN, COLON};

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

pub fn vec_to_string_add_four_spaces_at_beginning_of_each_line<T: fmt::Display>(vec: &Vec<T>, number_of_four_spaces: usize) -> String {
    to_string_and_add_four_spaces_at_beginning_of_each_line(&vec_to_string_with_sep(vec, "\n"), number_of_four_spaces)
}

pub fn add_four_spaces_at_beginning(str: &str, number_of_four_spaces: usize) -> String {
    format!("{}{}", "    ".repeat(number_of_four_spaces), str)
}

pub fn is_number_string_literally_integer_without_dot(str: &str) -> bool {
    !str.contains(DOT_AKA_FIELD_ACCESS_SIGN)
}

pub fn brace_vec_colon_vec_to_string<T: fmt::Display, T2: fmt::Display>(left: &Vec<T>, right: &Vec<T2>) -> String {
    if !left.is_empty() && !right.is_empty() {
        format!("{}{}{} {}{}", LEFT_BRACE, vec_to_string_with_sep(left, ", "), COLON, vec_to_string_with_sep(right, ", "), RIGHT_BRACE) 
    } else if right.is_empty() {
        format!("{}{}{}", LEFT_BRACE, vec_to_string_with_sep(left, ", "), RIGHT_BRACE)
    } else if left.is_empty() {
        format!("{}{}{}{}", LEFT_BRACE, COLON, vec_to_string_with_sep(right, ", "), RIGHT_BRACE)
    } else {
        format!("{}{}", LEFT_BRACE, RIGHT_BRACE)
    }
}

/// Returns true if the slice has at least one duplicate element.
pub fn vec_has_duplicates<T: Eq + Hash>(vec: &[T]) -> bool {
    let mut seen = HashSet::new();
    for item in vec.iter() {
        if !seen.insert(item) {
            return true;
        }
    }
    false
}