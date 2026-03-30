const BUILTIN_ENV_CODE_FOR_REAL_NUMBER_COMPARISON: &str = r#"
know:
    forall a, b R:
        a < b or a = b or a > b
        a < b or a >= b
        a > b or a <= b
        a <= b or a > b
        a >= b or a < b
        a <= b or a >= b
        a >= b or a <= b

    # its reverse is builtin, i.e. when we verify a <= b, the kernel will try verify a = b or a < b internally.
    forall a, b R:
        a <= b
        =>:
            a = b or a < b

    # its reverse is builtin, i.e. when we verify a >= b, the kernel will try verify a = b or a > b internally.
    forall a, b R:
        a >= b
        =>:
            a = b or a > b

    forall a R:
        exist b R st {a > b}
        exist b R st {a < b}
        exist b R st {a = b}
        exist b R st {a != b}
        exist b R st {a >= b}
        exist b R st {a <= b}

        exist b R st {b > a}
        exist b R st {b < a}
        exist b R st {b = a}
        exist b R st {b != a}
        exist b R st {b >= a}
        exist b R st {b <= a}

    exist a, b R st {a > b}
    exist a, b R st {a < b}
    exist a, b R st {a = b}
    exist a, b R st {a != b}
    exist a, b R st {a >= b}
    exist a, b R st {a <= b}

    exist a, b R st {b > a}
    exist a, b R st {b < a}
    exist a, b R st {b = a}
    exist a, b R st {b != a}
    exist a, b R st {b >= a}
    exist a, b R st {b <= a}
"#;

pub fn builtin_env_code() -> String {
    BUILTIN_ENV_CODE_FOR_REAL_NUMBER_COMPARISON.to_string()
}
