pub const BUILTIN_ENV_CODE_FOR_FUNDAMENTAL_COMPARISON: &str = r#"
know:
    forall a, b R:
        =>:
            a <= b
        <=>:
            0 <= b - a

    forall a R:
        0 <= a * a
        0 <= a^2

    forall a, b R:
        0 <= a
        0 <= b
        =>:
            0 <= a + b

    forall a, b R:
        0 <= a
        0 <= b
        =>:
            0 <= a * b
"#;
