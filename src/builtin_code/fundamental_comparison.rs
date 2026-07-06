// Fundamental order on R: difference characterization used by the verifier.
//
// Closure of the nonnegative / positive cone under +, *, /, and weak powers of nonnegative
// bases is implemented in Rust (`verify_order_atomic_fact_numeric_builtin_only` in
// `number_compare.rs`), not duplicated here.

pub const BUILTIN_ENV_CODE_FOR_FUNDAMENTAL_COMPARISON: &str = r#"
proof_debt:
    forall a, b R:
        a <= b
        =>:
            a = b or a < b

    forall a, b R:
        a >= b
        =>:
            a = b or a > b

    forall a, b R:
        =>:
            a <= b
        <=>:
            0 <= b - a

    forall a, b R:
        =>:
            a < b
        <=>:
            0 < b - a

    forall a R:
        a != 0
        =>:
            0 < a * a
            0 < a^2

    forall a, b R:
        a * b = 0
        =>:
            a = 0 or b = 0
"#;
