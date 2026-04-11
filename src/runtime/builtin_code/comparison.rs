// Order closure on R for +, -, *, / using only <= and < in conclusions (see also tmp.lit).

pub const BUILTIN_ENV_CODE_FOR_REAL_ARITHMETIC_ORDER_CLOSURE: &str = r#"
know:
    forall a, b, x R:
        0 <= x
        a <= b
        =>:
            a * x <= b * x
            x * a <= x * b

    forall a, b, x R:
        x <= 0
        a <= b
        =>:
            b * x <= a * x
            x * b <= x * a

    forall a, b, c, d R:
        a <= b
        c <= d
        =>:
            a + c <= b + d

    forall a, b, c, d R:
        a <= b
        c <= d
        =>:
            a - d <= b - c

    forall a, b, c, d R:
        a < b
        c < d
        =>:
            a + c < b + d

    forall a, b, c, d R:
        a <= b
        c < d
        =>:
            a + c < b + d

    forall a, b, c, d R:
        a < b
        c <= d
        =>:
            a + c < b + d

    forall a, b, x R:
        0 < x
        a < b
        =>:
            a * x < b * x
            x * a < x * b

    forall a, b, x R:
        0 < x
        a <= b
        =>:
            a * x <= b * x
            x * a <= x * b

    forall a, b, x R:
        x < 0
        a < b
        =>:
            b * x < a * x

    forall a, b, x R:
        x < 0
        a <= b
        =>:
            b * x <= a * x

    forall a, b, c R:
        0 < c
        a <= b
        =>:
            a / c <= b / c

    forall a, b, c R:
        0 < c
        a < b
        =>:
            a / c < b / c

    forall a, b, c R:
        c < 0
        a <= b
        =>:
            b / c <= a / c

    forall a, b, c R:
        c < 0
        a < b
        =>:
            b / c < a / c

    forall a, b R:
        a <= b
        =>:
            a - b <= 0

    forall a, b R:
        a - b <= 0
        =>:
            a <= b

    forall a, b R:
        a < b
        =>:
            a - b < 0

    forall a, b R:
        a - b < 0
        =>:
            a < b
"#;
