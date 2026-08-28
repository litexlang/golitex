//! Aggregate used by source-level tests for the split universal search engine.

pub(in crate::verification) const SOURCE: &str = concat!(
    include_str!("../../../src/verification/atomic/universal_search/mod.rs"),
    include_str!("../../../src/verification/atomic/universal_search/anonymous_function_alpha.rs"),
    include_str!("../../../src/verification/atomic/universal_search/anonymous_function_bodies.rs"),
    include_str!("../../../src/verification/atomic/universal_search/argument_combinations.rs"),
    include_str!("../../../src/verification/atomic/universal_search/argument_shapes.rs"),
    include_str!("../../../src/verification/atomic/universal_search/arithmetic_arguments.rs"),
    include_str!("../../../src/verification/atomic/universal_search/binder_arguments.rs"),
    include_str!("../../../src/verification/atomic/universal_search/collection_arguments.rs"),
    include_str!(
        "../../../src/verification/atomic/universal_search/finite_set_measure_arguments.rs"
    ),
    include_str!(
        "../../../src/verification/atomic/universal_search/function_collection_arguments.rs"
    ),
    include_str!(
        "../../../src/verification/atomic/universal_search/interval_sequence_arguments.rs"
    ),
    include_str!("../../../src/verification/atomic/universal_search/iterated_arguments.rs"),
    include_str!("../../../src/verification/atomic/universal_search/matcher_dispatch.rs"),
    include_str!("../../../src/verification/atomic/universal_search/matcher_state.rs"),
    include_str!("../../../src/verification/atomic/universal_search/matrix_index_arguments.rs"),
    include_str!("../../../src/verification/atomic/universal_search/search.rs"),
    include_str!("../../../src/verification/atomic/universal_search/set_operation_arguments.rs"),
    include_str!("../../../src/verification/atomic/universal_search/tuple_arguments.rs"),
);
