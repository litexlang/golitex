//! Tests for compositional object well-definedness.

use super::*;

#[test]
fn compositional_well_definedness_cache_returns_exact_reuse_source() {
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
    assert!(Rc::ptr_eq(&reuse.source, &first));
    assert_eq!(reuse.object.to_string(), object.to_string());
}

#[test]
fn ordinary_well_definedness_keeps_historical_active_reentry_suppression() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("ordinary-active-wd-reentry.lit");
    let object: Obj = Number::new("1".to_string()).into();
    runtime.begin_well_defined_object(&obj_equality_key(&object));

    runtime
        .verify_obj_well_defined_and_store_cache(&object, &VerifyState::initial())
        .expect("ordinary Litex verification should retain active-object suppression");
}
