//! Aggregate used by source-level tests for the split equality dispatcher.

pub(in crate::verification) const SOURCE: &str = concat!(
    include_str!("../../../src/verification/builtin_rules/equality_dispatch/dispatch.rs"),
    include_str!(
        "../../../src/verification/builtin_rules/equality_dispatch/division_and_products.rs"
    ),
    include_str!("../../../src/verification/builtin_rules/equality_dispatch/empty_sets.rs"),
    include_str!(
        "../../../src/verification/builtin_rules/equality_dispatch/finite_set_cardinality.rs"
    ),
    include_str!(
        "../../../src/verification/builtin_rules/equality_dispatch/indexed_set_families.rs"
    ),
    include_str!(
        "../../../src/verification/builtin_rules/equality_dispatch/literal_set_intersections.rs"
    ),
    include_str!(
        "../../../src/verification/builtin_rules/equality_dispatch/registered_antisymmetry.rs"
    ),
    include_str!("../../../src/verification/builtin_rules/equality_dispatch/set_builders.rs"),
    include_str!("../../../src/verification/builtin_rules/equality_dispatch/set_operations.rs"),
    include_str!("../../../src/verification/builtin_rules/equality_dispatch/subtraction.rs"),
    include_str!(
        "../../../src/verification/builtin_rules/equality_dispatch/tuple_reconstruction.rs"
    ),
    include_str!(
        "../../../src/verification/builtin_rules/equality_dispatch/tuples_and_cartesian.rs"
    ),
    include_str!("../../../src/verification/builtin_rules/equality_dispatch/two_sided_order.rs"),
);
