use super::defaults::DEFAULT_MANGLED_FN_PARAM_PREFIX;
use super::keywords::is_keyword;

const MAX_NAME_LEN: usize = 255;

pub fn is_valid_litex_name(s: &str) -> Result<(), String> {
    if s.is_empty() {
        return Err("name cannot be empty".to_string());
    }
    if s.starts_with(DEFAULT_MANGLED_FN_PARAM_PREFIX) {
        return Err(format!(
            "user defined name cannot start with two underscores because it is reserved for internal use: `{}`.",
            s
        ));
    }
    if s.len() > MAX_NAME_LEN {
        return Err(format!(
            "name length cannot be greater than {}, current length is {}",
            MAX_NAME_LEN,
            s.len()
        ));
    }
    let mut chars = s.chars();
    let first = chars.next();

    if let Some(first) = first {
        if first != '_' && !first.is_alphabetic() {
            return Err(format!(
                "name first character cannot be a number or symbol, Got: {:?}",
                first
            ));
        }
    }

    for c in chars {
        if c != '_' && !c.is_alphanumeric() {
            return Err(format!(
                "name can only contain letters, numbers and underscores, illegal character: {:?}",
                c
            ));
        }
    }
    if is_keyword(s) {
        return Err(format!("cannot use keyword as name: {}", s));
    }
    Ok(())
}

#[cfg(test)]
#[path = "../../tests/unit/common/is_valid_litex_name/tests.rs"]
mod tests;
