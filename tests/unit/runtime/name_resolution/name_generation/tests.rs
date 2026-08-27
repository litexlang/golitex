//! Contracts for internal Runtime name generation.

use crate::prelude::*;

#[test]
fn generated_kernel_binders_are_unique_and_not_user_names() {
    let runtime = Runtime::default();
    let first = runtime.generate_random_unused_name();
    let second = runtime.generate_random_unused_name();

    assert_ne!(first, second);
    assert!(first.starts_with(INTERNAL_BINDER_PREFIX));
    assert!(is_valid_litex_name(&first).is_err());
}

#[test]
fn allocated_internal_binder_name_preserves_its_symbol_id() {
    let runtime = Runtime::default();
    let generated = runtime.allocate_internal_symbol_binding().unwrap();
    let reconstructed = runtime
        .allocate_local_symbol_binding(generated.name().to_string())
        .unwrap();

    assert_eq!(generated.id(), reconstructed.id());
    assert!(generated.name().starts_with(INTERNAL_BINDER_PREFIX));
}
