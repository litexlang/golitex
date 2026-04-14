pub const BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS: &str = r#"
know:
    forall x R:
        0 <= abs(x)
        abs(x) = x or abs(x) = -x

    forall x, y R:
        abs(x * y) = abs(x) * abs(y)

have fn max(x, y R) R:
    case x >= y: x
    case x < y: y

know:
    forall x, y R:
        x <= max(x, y)
        y <= max(x, y)
        max(x, y) = x or max(x, y) = y

have fn min(x, y R) R:
    case x <= y: x
    case x > y: y

know:
    forall x, y R:
        min(x, y) <= x
        min(x, y) <= y
        min(x, y) = x or min(x, y) = y
"#;
