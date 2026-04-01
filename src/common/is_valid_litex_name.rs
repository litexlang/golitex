use super::keywords::is_keyword;

const MAX_NAME_LEN: usize = 255;

pub fn is_valid_litex_name(s: &str) -> Result<(), String> {
    if s.is_empty() {
        return Err("name cannot be empty".to_string());
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
mod tests {
    use super::*;

    #[test]
    fn empty_rejected() {
        assert!(is_valid_litex_name("").is_err());
    }

    #[test]
    fn keyword_rejected() {
        assert!(is_valid_litex_name("let").is_err());
        assert!(is_valid_litex_name("prop").is_err());
        assert!(is_valid_litex_name("abstract_prop").is_err());
        assert!(is_valid_litex_name("exist").is_err());
        assert!(is_valid_litex_name("R").is_err());
        assert!(is_valid_litex_name("in").is_err());
    }

    #[test]
    fn first_char_digit_rejected() {
        assert!(is_valid_litex_name("0abc").is_err());
        assert!(is_valid_litex_name("9x").is_err());
        assert!(is_valid_litex_name("1").is_err());
    }

    #[test]
    fn first_char_symbol_rejected() {
        assert!(is_valid_litex_name("+foo").is_err());
        assert!(is_valid_litex_name("-bar").is_err());
        assert!(is_valid_litex_name("*x").is_err());
        assert!(is_valid_litex_name(".a").is_err());
        assert!(is_valid_litex_name("=").is_err());
    }

    #[test]
    fn max_length_255() {
        let ok_255: String = "a".chars().cycle().take(255).collect();
        assert!(is_valid_litex_name(&ok_255).is_ok());
        let bad_256: String = "a".chars().cycle().take(256).collect();
        assert!(is_valid_litex_name(&bad_256).is_err());
    }

    #[test]
    fn underscore_and_letters_allowed() {
        assert!(is_valid_litex_name("_").is_ok());
        assert!(is_valid_litex_name("_x").is_ok());
        assert!(is_valid_litex_name("a_b_c").is_ok());
        assert!(is_valid_litex_name("Abc").is_ok());
        assert!(is_valid_litex_name("名字").is_ok());
        assert!(is_valid_litex_name("变量_1").is_ok());
        assert!(is_valid_litex_name("x1").is_ok());
    }

    #[test]
    fn symbols_rejected() {
        assert!(is_valid_litex_name("a+b").is_err());
        assert!(is_valid_litex_name("a-b").is_err());
        assert!(is_valid_litex_name("a*b").is_err());
        assert!(is_valid_litex_name("a.b").is_err());
        assert!(is_valid_litex_name("a(b)").is_err());
        assert!(is_valid_litex_name("a[b]").is_err());
        assert!(is_valid_litex_name("a:b").is_err());
        assert!(is_valid_litex_name("a,b").is_err());
        assert!(is_valid_litex_name("a b").is_err());
    }

    #[test]
    fn valid_english_and_chinese() {
        assert!(is_valid_litex_name("foo").is_ok());
        assert!(is_valid_litex_name("FooBar").is_ok());
        assert!(is_valid_litex_name("定理").is_ok());
        assert!(is_valid_litex_name("定理_1").is_ok());
        assert!(is_valid_litex_name("α").is_ok());
    }
}
