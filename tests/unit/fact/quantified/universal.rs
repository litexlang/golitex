//! Universal fact binder-identity contracts.

use crate::prelude::*;

fn set_param(runtime: &Runtime, name: &str) -> TypedParameterList {
    TypedParameterList::new(vec![runtime
        .fresh_param_group_with_type(vec![name.to_string()], ParamType::Set(Set::new()))
        .unwrap()])
}

#[test]
fn canonical_forall_rejects_nested_premise_reusing_outer_param() {
    let runtime = Runtime::default();
    let inner = ForallFact::new_canonical_forall(
        set_param(&runtime, "x"),
        vec![],
        vec![],
        default_line_file(),
    )
    .unwrap();

    let outer = ForallFact::new_canonical_forall(
        set_param(&runtime, "x"),
        vec![inner.into()],
        vec![],
        default_line_file(),
    );

    assert!(outer.is_err());
}
