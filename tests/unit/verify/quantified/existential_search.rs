//! Tests for existential search through known universal facts.

use super::*;

#[test]
fn detects_nested_exist_witness_dependency() {
    let runtime = Runtime::new();
    let names = vec!["x".to_string()];
    let binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let witness: Obj = ExistFreeParamObj::new(&binding).into();
    let external: Obj = Identifier::new("a".to_string()).into();
    let nested: Obj = Union::new(witness, external.clone()).into();

    assert!(Runtime::obj_depends_on_given_exist_param(&nested, &names));
    assert!(!Runtime::obj_depends_on_given_exist_param(
        &external, &names
    ));
}

#[test]
fn detects_function_call_on_exist_witness() {
    let runtime = Runtime::new();
    let names = vec!["x".to_string()];
    let binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let head: FnObjHead = ExistFreeParamObj::new(&binding).into();
    let arg: Obj = Number::new("1".to_string()).into();
    let fn_obj: Obj = FnObj::new(head, vec![vec![Box::new(arg)]]).into();

    assert!(Runtime::obj_depends_on_given_exist_param(&fn_obj, &names));
}

#[test]
fn existential_binding_validation_preserves_binder_kind() {
    let runtime = Runtime::new();
    let exist_binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let forall_binding = runtime
        .allocate_local_symbol_binding("x".to_string())
        .unwrap();
    let exist: Obj = ExistFreeParamObj::new(&exist_binding).into();
    let captured_forall: Obj = ForallFreeParamObj::new(&forall_binding).into();

    assert!(Runtime::obj_matches_exist_forall_binding_name(&exist, "x"));
    assert!(!Runtime::obj_matches_exist_forall_binding_name(
        &captured_forall,
        "x"
    ));
}
