//! Aggregate used by source-level tests for split numeric order verification.

pub(in crate::verification) const SOURCE: &str = concat!(
    include_str!("../../../src/verification/builtin_rules/number_compare/mod.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/additive_sign.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/decimal_comparison.rs"),
    include_str!(
        "../../../src/verification/builtin_rules/number_compare/finite_set_cardinality.rs"
    ),
    include_str!(
        "../../../src/verification/builtin_rules/number_compare/integer_membership_bounds.rs"
    ),
    include_str!("../../../src/verification/builtin_rules/number_compare/known_numeric_bounds.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/logarithm_order.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/modulo_bounds.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/multiplicative_sign.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/numeric_dispatch.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/order_equivalences.rs"),
    include_str!("../../../src/verification/builtin_rules/number_compare/power_sign.rs"),
    include_str!(
        "../../../src/verification/builtin_rules/number_compare/roots_and_absolute_value.rs"
    ),
    include_str!("../../../src/verification/builtin_rules/number_compare/subtraction_order.rs"),
);
