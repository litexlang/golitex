pub const BUILTIN_ENV_CODE: &str = r#"
know:
    forall a, b R:
        a < b or a = b or a > b
        a < b or a >= b
        a > b or a <= b
        a <= b or a > b
        a >= b or a < b
        a <= b or a >= b
        a >= b or a <= b

    forall a, b R:
        =>:
            a <= b
        <=>:
            a = b or a < b

    forall a, b R:
        =>:
            a >= b
        <=>:
            a = b or a > b
"#;
