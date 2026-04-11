pub const BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS: &str = r#"
have fn abs(x R) R:
    case x >= 0: x
    case x < 0: -x

have fn max(x, y R) R:
    case x >= y: x
    case x < y: y

have fn min(x, y R) R:
    case x <= y: x
    case x > y: y

family seq(s set) = Fn(N_pos) s
family finite_seq(s set, n N_pos) = fn(x N_pos: x <= n) s
"#;
