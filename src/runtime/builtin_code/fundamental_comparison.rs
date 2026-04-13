// Fundamental order on R: difference characterization, nonnegative cone, quotients;
// and <= / >= decomposition used by the verifier.

pub const BUILTIN_ENV_CODE_FOR_FUNDAMENTAL_COMPARISON: &str = r#"
know:
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
        0 <= a * a
        0 <= a^2

    forall a R:
        a != 0
        =>:
            0 < a * a
            0 < a^2

    forall a, b R:
        0 < a and 0 <= b or 0 <= a and 0 < b
        =>:
            0 < a + b

    forall a, b R:
        0 <= a
        0 <= b
        =>:
            0 <= a * b

    forall a, b R:
        0 < a
        0 < b
        =>:
            0 < a * b

    forall a, b R:
        0 <= a
        0 < b
        =>:
            0 <= a / b

    forall a, b R:
        0 < a
        0 < b
        =>:
            0 < a / b
"#;
