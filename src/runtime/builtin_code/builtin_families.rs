pub const BUILTIN_ENV_CODE_FOR_BUILTIN_FAMILIES: &str = r#"
family seq(s set) = Fn(N_pos) s
family finite_seq(s set, n N_pos) = fn(x N_pos: x <= n) s
"#;
