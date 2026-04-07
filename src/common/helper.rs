use super::defaults::DEFAULT_MANGLED_FN_PARAM_PREFIX;
use super::keywords::{
    COLON, DOT_AKA_FIELD_ACCESS_SIGN, LEFT_BRACE, LEFT_CURLY_BRACE, RIGHT_BRACE, RIGHT_CURLY_BRACE,
};
use std::fmt::{self};

pub fn braced_vec_to_string<T: fmt::Display>(vec: &Vec<T>) -> String {
    format!(
        "{}{}{}",
        LEFT_BRACE,
        vec_to_string_with_sep(vec, ", ".to_string()),
        RIGHT_BRACE
    )
}

pub fn curly_braced_vec_to_string<T: fmt::Display>(vec: &Vec<T>) -> String {
    format!(
        "{}{}{}",
        LEFT_CURLY_BRACE,
        vec_to_string_with_sep(vec, ", ".to_string()),
        RIGHT_CURLY_BRACE
    )
}

pub fn vec_to_string_with_sep<T: fmt::Display>(vec: &Vec<T>, sep: String) -> String {
    vec.iter()
        .map(|x| x.to_string())
        .collect::<Vec<String>>()
        .join(sep.as_str())
}

pub fn braced_string<T: fmt::Display>(str: &T) -> String {
    format!("{}{}{}", LEFT_BRACE, str, RIGHT_BRACE)
}

pub fn vec_pair_to_string<A: fmt::Display, B: fmt::Display>(
    left: &Vec<A>,
    right: &Vec<B>,
) -> String {
    if left.len() != right.len() {
        unreachable!("left and right must have the same length");
    }
    left.iter()
        .zip(right.iter())
        .map(|(l, r)| format!("{} {}", l, r))
        .collect::<Vec<String>>()
        .join(", ")
}

pub fn to_string_and_add_four_spaces_at_beginning_of_each_line<T: fmt::Display>(
    fact: &T,
    number_of_four_spaces: usize,
) -> String {
    fact.to_string()
        .split("\n")
        .map(|fact| format!("{}{}", "    ".repeat(number_of_four_spaces), fact))
        .collect::<Vec<String>>()
        .join("\n")
}

pub fn curly_braced_vec_to_string_with_sep<T: fmt::Display>(vec: &Vec<T>, sep: String) -> String {
    format!(
        "{}{}{}",
        LEFT_CURLY_BRACE,
        vec_to_string_with_sep(vec, sep),
        RIGHT_CURLY_BRACE
    )
}

pub fn vec_to_string_join_by_comma<T: fmt::Display>(vec: &Vec<T>) -> String {
    vec.iter()
        .map(|x| x.to_string())
        .collect::<Vec<String>>()
        .join(", ")
}

/// `fn` / 内涵集 AST 中形参存为 `__` + 用户符面；打印时去掉此前缀。
pub fn comma_separated_stored_fn_params_as_user_source(params: &[String]) -> String {
    params
        .iter()
        .map(|p| {
            p.strip_prefix(DEFAULT_MANGLED_FN_PARAM_PREFIX)
                .map(String::from)
                .unwrap_or_else(|| p.clone())
        })
        .collect::<Vec<_>>()
        .join(", ")
}

pub fn vec_to_string_add_four_spaces_at_beginning_of_each_line<T: fmt::Display>(
    vec: &Vec<T>,
    number_of_four_spaces: usize,
) -> String {
    to_string_and_add_four_spaces_at_beginning_of_each_line(
        &vec_to_string_with_sep(vec, "\n".to_string()),
        number_of_four_spaces,
    )
}

pub fn add_four_spaces_at_beginning(str: String, number_of_four_spaces: usize) -> String {
    format!("{}{}", "    ".repeat(number_of_four_spaces), str)
}

pub fn is_number_string_literally_integer_without_dot(str: String) -> bool {
    !str.contains(DOT_AKA_FIELD_ACCESS_SIGN)
}

pub fn brace_vec_colon_vec_to_string<T: fmt::Display, T2: fmt::Display>(
    left: &Vec<T>,
    right: &Vec<T2>,
) -> String {
    let sep = ", ".to_string();
    if !left.is_empty() && !right.is_empty() {
        format!(
            "{}{}{} {}{}",
            LEFT_BRACE,
            vec_to_string_with_sep(left, sep.clone()),
            COLON,
            vec_to_string_with_sep(right, sep),
            RIGHT_BRACE
        )
    } else if right.is_empty() {
        format!(
            "{}{}{}",
            LEFT_BRACE,
            vec_to_string_with_sep(left, sep),
            RIGHT_BRACE
        )
    } else if left.is_empty() {
        format!(
            "{}{}{}{}",
            LEFT_BRACE,
            COLON,
            vec_to_string_with_sep(right, sep),
            RIGHT_BRACE
        )
    } else {
        format!("{}{}", LEFT_BRACE, RIGHT_BRACE)
    }
}

pub fn todo_error_message(context: String) -> String {
    format!("TODO: {} is not implemented yet", context)
}

pub fn remove_windows_carriage_return(source_code: &str) -> String {
    source_code.replace('\r', "")
}
