// Common comparison properties: trichotomy and witnesses on R, zero-product, transitivity
// (props + know), and order closure under +, -, *, / (conclusions use only <= and <).

pub const KNOW_REAL_LINE_TRICHOTOMY: &str = r#"
know:
    forall a, b R:
        a < b or a = b or a > b
        a > b or a = b or a < b
        a < b or a >= b
        a > b or a <= b
        a <= b or a > b
        a >= b or a < b
        a <= b or a >= b
        a >= b or a <= b

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

    forall a, b R:
        a * b = 0
        =>:
            a = 0 or b = 0
"#;

pub const ORDER_TRANSITIVITY_PROP_DECLS: &str = r#"

prop a_lt_c(a, b, c R):
    a < c

prop a_le_c(a, b, c R):
    a <= c

prop a_gt_c(a, b, c R):
    a > c

prop a_ge_c(a, b, c R):
    a >= c
"#;

pub const KNOW_ORDER_TRANSITIVITY_CHAIN: &str = r#"
know:
    forall a, b, c R:
        a < b
        b < c
        =>:
            $a_lt_c(a, b, c)

    forall a, b, c R:
        a <= b
        b <= c
        =>:
            $a_le_c(a, b, c)

    forall a, b, c R:
        a > b
        b > c
        =>:
            $a_gt_c(a, b, c)

    forall a, b, c R:
        a >= b
        b >= c
        =>:
            $a_ge_c(a, b, c)
"#;

pub const BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES: &str = r#"
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
