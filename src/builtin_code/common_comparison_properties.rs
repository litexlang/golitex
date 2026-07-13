// Common comparison properties: trichotomy and witnesses on R, zero-product, named
// transitivity theorems, and difference characterization (`a - b` vs `0`).
// Order closure under +, -, *, / on general inequalities is in `order_algebra_builtin.rs`.

// Real-line trichotomy in common display orders.
// Example: `forall x, y R: x = y or x < y or x > y`.
pub const TRUST_REAL_LINE_TRICHOTOMY: &str = r#"
trust:
    forall a, b R:
        a = b or a < b or a > b
        a = b or a > b or a < b
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

pub const ORDER_TRANSITIVITY_THMS: &str = r#"

thm a_lt_c:
    ? forall a, b, c R:
        a < b
        b < c
        =>:
            a < c
    a < b < c

# Mixed transitivity on R. Example: `a <= b` and `b < c` yield `a < c`.
thm a_le_lt_c:
    ? forall a, b, c R:
        a <= b
        b < c
        =>:
            a < c
    trust a < c

# Mixed transitivity on R. Example: `a < b` and `b <= c` yield `a < c`.
thm a_lt_le_c:
    ? forall a, b, c R:
        a < b
        b <= c
        =>:
            a < c
    trust a < c

thm a_le_c:
    ? forall a, b, c R:
        a <= b
        b <= c
        =>:
            a <= c
    a <= b <= c

thm a_gt_c:
    ? forall a, b, c R:
        a > b
        b > c
        =>:
            a > c
    a > b > c

thm a_ge_c:
    ? forall a, b, c R:
        a >= b
        b >= c
        =>:
            a >= c
    a >= b >= c
"#;

pub const BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES: &str = r#"
trust:
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
