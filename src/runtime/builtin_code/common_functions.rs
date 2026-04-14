pub const BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS: &str = r#"
know:
    forall x R:
        0 <= abs(x)
        abs(x) = x or abs(x) = -x

    forall x, y R:
        abs(x * y) = abs(x) * abs(y)

know:
    forall x, y R:
        x <= max(x, y)
        y <= max(x, y)

know:
    forall x, y R:
        min(x, y) <= x
        min(x, y) <= y
"#;
