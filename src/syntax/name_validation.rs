use super::keywords::is_keyword;
use super::source_conventions::INTERNAL_SYMBOL_PREFIX;

const MAX_NAME_LEN: usize = 255;

pub fn is_valid_litex_name(s: &str) -> Result<(), String> {
    if s.is_empty() {
        return Err("name cannot be empty".to_string());
    }
    if s.starts_with(INTERNAL_SYMBOL_PREFIX) {
        return Err(format!(
            "user-defined names cannot start with `{}` because that prefix is reserved for Litex internals: `{}`",
            INTERNAL_SYMBOL_PREFIX, s
        ));
    }
    if s.contains('#') {
        return Err(format!(
            "name cannot contain `#` because `#` starts a line comment: {}",
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
#[path = "../../tests/unit/syntax/name_validation/tests.rs"]
mod tests;
