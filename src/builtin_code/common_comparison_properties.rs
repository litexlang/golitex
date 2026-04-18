// Common comparison properties: trichotomy and witnesses on R, zero-product, transitivity
// (props + know), and difference characterization (`a - b` vs `0`).
// Order closure under +, -, *, / on general inequalities is in `order_algebra_builtin.rs`.

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

    forall a, b, c R:
        0 < c
        c * a <= b or a * c <= b
        =>:
            a <= b / c

    forall a, b, c R:
        0 < c
        a / c <= b
        =>:
            a <= b * c

    forall a, b Z:
        a <= b
        =>:
            count(closed_range(a, b)) = b - a + 1

    forall a, b Z:
        a < b
        =>:
            count(range(a, b)) = b - a   
"#;
