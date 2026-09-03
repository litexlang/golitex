//! Tests for compositional object well-definedness.

use super::*;

#[test]
fn compositional_well_definedness_memo_returns_exact_reuse_source() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("compositional-wd-reuse.lit");
    let object: Obj = Number::new("1".to_string()).into();
    let verify_state = VerifyState::initial();

    let first = runtime
        .verify_obj_well_defined_result(&object, &verify_state)
        .expect("first object check succeeds");
    assert!(matches!(
        first.as_ref(),
        SuccessVerifyObjWellDefinedResult::Direct(_)
    ));

    let second = runtime
        .verify_obj_well_defined_result(&object, &verify_state)
        .expect("second object check reuses the first proof");
    let SuccessVerifyObjWellDefinedResult::Reuse(reuse) = second.as_ref() else {
        panic!("second object check must be an explicit Reuse node");
    };
    let SuccessVerifyObjWellDefinedResult::Direct(first_direct) = first.as_ref() else {
        unreachable!("validated above")
    };
    assert!(Rc::ptr_eq(&reuse.source, first_direct));
    assert_eq!(reuse.object.to_string(), object.to_string());
}

#[test]
fn active_well_definedness_reentry_is_an_error() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("ordinary-active-wd-reentry.lit");
    let object: Obj = Number::new("1".to_string()).into();
    let verify_state = VerifyState::initial();
    verify_state.begin_well_defined_object(&obj_equality_key(&object));

    let error = runtime
        .verify_obj_well_defined_result(&object, &verify_state)
        .expect_err("active object WD re-entry must not fabricate successful evidence");
    assert!(format!("{error:?}").contains("cyclic"), "{error:?}");
}
