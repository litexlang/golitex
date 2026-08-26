use super::*;

#[test]
fn collects_forall_name_from_function_head() {
    let runtime = Runtime::default();
    let function_binding = runtime
        .allocate_local_symbol_binding("function".to_string())
        .unwrap();
    let object: Obj = FnObj::new(
        BoundParamObj::new(&function_binding).into(),
        vec![vec![Box::new(forall_obj(&runtime, "argument"))]],
    )
    .into();

    assert_eq!(
        object.collect_forall_free_param_names(),
        HashSet::from(["function".to_string(), "argument".to_string()])
    );
}

#[test]
fn collects_bound_function_head_names_without_source_kinds() {
    let runtime = Runtime::default();
    let builder_head = runtime
        .allocate_local_symbol_binding("builder_head".to_string())
        .unwrap();
    let fn_argument = runtime
        .allocate_local_symbol_binding("fn_argument".to_string())
        .unwrap();
    let fn_head = runtime
        .allocate_local_symbol_binding("fn_head".to_string())
        .unwrap();
    let builder_argument = runtime
        .allocate_local_symbol_binding("builder_argument".to_string())
        .unwrap();
    let set_builder_head: Obj = FnObj::new(
        BoundParamObj::new(&builder_head).into(),
        vec![vec![Box::new(BoundParamObj::new(&fn_argument).into())]],
    )
    .into();
    let fn_set_head: Obj = FnObj::new(
        BoundParamObj::new(&fn_head).into(),
        vec![vec![Box::new(BoundParamObj::new(&builder_argument).into())]],
    )
    .into();
    let object: Obj = ListSet::new(vec![set_builder_head, fn_set_head]).into();

    assert_eq!(
        object.collect_bound_param_names(),
        HashSet::from([
            "builder_head".to_string(),
            "builder_argument".to_string(),
            "fn_head".to_string(),
            "fn_argument".to_string(),
        ])
    );
}

#[test]
fn collects_fn_set_and_anonymous_function_binder_headers() {
    let runtime = Runtime::default();
    let fn_set: Obj = FnSet::new(
        vec![runtime
            .fresh_param_group_with_set(vec!["fn_bound".to_string()], StandardSet::R.into())
            .unwrap()],
        vec![],
        StandardSet::R.into(),
    )
    .unwrap()
    .into();
    let anonymous_fn: Obj = AnonymousFn::new(
        vec![runtime
            .fresh_param_group_with_set(vec!["anonymous_bound".to_string()], StandardSet::R.into())
            .unwrap()],
        vec![],
        StandardSet::R.into(),
        Number::new("0".to_string()).into(),
    )
    .unwrap()
    .into();
    let object: Obj = ListSet::new(vec![fn_set, anonymous_fn]).into();

    assert_eq!(
        object.collect_bound_param_names(),
        HashSet::from(["fn_bound".to_string(), "anonymous_bound".to_string()])
    );
}

fn forall_obj(runtime: &Runtime, name: &str) -> Obj {
    let binding = runtime
        .allocate_local_symbol_binding(name.to_string())
        .unwrap();
    BoundParamObj::new(&binding).into()
}
