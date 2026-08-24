use crate::prelude::*;

#[test]
fn generated_kernel_binders_are_unique_and_not_user_names() {
    let runtime = Runtime::new();
    let first = runtime.generate_random_unused_name();
    let second = runtime.generate_random_unused_name();

    assert_ne!(first, second);
    assert!(first.starts_with("#binder_"));
    assert!(is_valid_litex_name(&first).is_err());
}
