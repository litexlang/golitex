//! Tests for existential search through known universal facts.

use super::*;

#[test]
fn detects_nested_exist_witness_dependency() {
    let runtime = Runtime::default();
    let binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let symbol_ids = vec![binding.id()];
    let witness: Obj = BoundParamObj::new(&binding).into();
    let external: Obj = Identifier::new("a".to_string()).into();
    let nested: Obj = Union::new(witness, external.clone()).into();

    assert!(Runtime::obj_depends_on_given_exist_param(
        &nested,
        &symbol_ids
    ));
    assert!(!Runtime::obj_depends_on_given_exist_param(
        &external,
        &symbol_ids
    ));
}

#[test]
fn detects_function_call_on_exist_witness() {
    let runtime = Runtime::default();
    let binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let symbol_ids = vec![binding.id()];
    let head: FnObjHead = BoundParamObj::new(&binding).into();
    let arg: Obj = Number::new("1".to_string()).into();
    let fn_obj: Obj = FnObj::new(head, vec![vec![Box::new(arg)]]).into();

    assert!(Runtime::obj_depends_on_given_exist_param(
        &fn_obj,
        &symbol_ids
    ));
}

#[test]
fn existential_binding_validation_uses_exact_symbol_identity() {
    let runtime = Runtime::default();
    let exist_binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let forall_binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let exist: Obj = BoundParamObj::new(&exist_binding).into();
    let captured_forall: Obj = BoundParamObj::new(&forall_binding).into();

    assert!(Runtime::obj_matches_exist_forall_binding(
        &exist,
        exist_binding.id()
    ));
    assert!(!Runtime::obj_matches_exist_forall_binding(
        &captured_forall,
        exist_binding.id()
    ));
}
