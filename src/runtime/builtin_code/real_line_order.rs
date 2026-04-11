// Trichotomy, <= / >= decomposition, existential witnesses on R, zero-product, and transitivity props+know.

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

    # its reverse is builtin, i.e. when we verify a <= b, the kernel will try verify a = b or a < b internally.
    forall a, b R:
        a <= b
        =>:
            a = b or a < b

    # its reverse is builtin, i.e. when we verify a >= b, the kernel will try verify a = b or a > b internally.
    forall a, b R:
        a >= b
        =>:
            a = b or a > b

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
