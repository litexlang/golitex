use super::*;

fn store_compiler_equality(runtime: &mut Runtime, left: Obj, right: Obj, fact_id: FactId) {
    let equality = EqualFact::new(left, right, default_line_file());
    runtime
        .top_level_env()
        .store_equality(&equality)
        .expect("store equality proof edge");
    runtime
        .top_level_env()
        .store_fact_to_cache_known_fact(equality.to_string(), default_line_file(), fact_id)
        .expect("store equality FactId");
}

fn matcher_accepts_with_one_known_leaf(left: &Obj, right: &Obj, x: &Obj, y: &Obj) -> bool {
    Runtime::same_shape_and_corresponding_args_match(left, right, &mut |left_arg, right_arg| {
        Ok::<bool, ()>(
            objs_match_for_pattern(left_arg, right_arg)
                || (objs_match_for_pattern(left_arg, x) && objs_match_for_pattern(right_arg, y)),
        )
    })
    .expect("structural matching is infallible in this test")
}

#[test]
fn central_matcher_covers_obligation_free_complex_and_general_cart_congruence() {
    let x: Obj = Identifier::new("x".to_string()).into();
    let y: Obj = Identifier::new("y".to_string()).into();
    let index_set: Obj = Identifier::new("I".to_string()).into();
    let family_set: Obj = Identifier::new("S".to_string()).into();

    let pairs: Vec<(Obj, Obj)> = vec![
        (
            RealPart::new(x.clone()).into(),
            RealPart::new(y.clone()).into(),
        ),
        (
            ImaginaryPart::new(x.clone()).into(),
            ImaginaryPart::new(y.clone()).into(),
        ),
        (
            ComplexAbs::new(x.clone()).into(),
            ComplexAbs::new(y.clone()).into(),
        ),
        (
            GeneralCart::new(index_set.clone(), family_set.clone(), x.clone()).into(),
            GeneralCart::new(index_set, family_set, y.clone()).into(),
        ),
    ];

    for (left, right) in pairs {
        assert!(
            matcher_accepts_with_one_known_leaf(&left, &right, &x, &y),
            "central structural matcher should descend through {left} and {right}"
        );
    }
}

#[test]
fn pure_congruence_and_definitional_reduction_are_not_ordinary_equality_builtins() {
    let dispatch = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verify/verify_builtin_rules/equality_dispatch.rs"
    ));
    let function_rules = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verify/verify_builtin_rules/equality_function.rs"
    ));
    let complex_rules = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verify/verify_builtin_rules/complex_builtin.rs"
    ));
    let sqrt_rules = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verify/verify_builtin_rules/equality_numeric/square_root.rs"
    ));
    let abs_rules = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs"
    ));
    let numeric_modules = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verify/verify_builtin_rules/equality_numeric/mod.rs"
    ));

    for removed_entry in [
        "try_verify_same_algebra_context_by_equal_args",
        "try_verify_projection_from_known_tuple_equality",
        "try_verify_anonymous_fn_application_equals_other_side",
        "anonymous fn: identical surface syntax",
    ] {
        assert!(
            !dispatch.contains(removed_entry),
            "ordinary equality dispatch still contains `{removed_entry}`"
        );
    }
    assert!(!function_rules.contains("substitute args into the body"));
    assert!(!complex_rules.contains("coordinates respect complex equality"));
    assert!(!sqrt_rules.contains("try_verify_sqrt_equal_args_identity"));
    assert!(!abs_rules.contains("try_verify_abs_sign_invariance"));
    assert!(!numeric_modules.contains("mod algebra_context"));
}

#[test]
fn compiler_equality_evidence_does_not_leak_from_discarded_child() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("compiler-equality-discarded-child");
    let a: Obj = Identifier::new("a".to_string()).into();
    let b: Obj = Identifier::new("b".to_string()).into();
    let c: Obj = Identifier::new("c".to_string()).into();
    store_compiler_equality(&mut runtime, a.clone(), b.clone(), FactId::new(1));

    let result: Result<(), RuntimeError> = runtime.run_in_local_env(|runtime| {
        store_compiler_equality(runtime, b.clone(), c.clone(), FactId::new(2));
        assert!(runtime
            .compiler_known_equality_path(&EqualFact::new_from_refs(&a, &c, default_line_file(),))
            .is_some());
        Ok(())
    });
    result.expect("discarded-child evidence probe should run");
    assert!(runtime
        .compiler_known_equality_path(&EqualFact::new_from_refs(&a, &c, default_line_file(),))
        .is_none());
}

#[test]
fn compiler_equality_evidence_requires_a_cached_fact_id() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("compiler-equality-missing-fact-id");
    let a: Obj = Identifier::new("a".to_string()).into();
    let b: Obj = Identifier::new("b".to_string()).into();
    runtime
        .top_level_env()
        .store_equality(&EqualFact::new(a.clone(), b.clone(), default_line_file()))
        .expect("store semantic equality without compiler identity");

    assert!(runtime
        .compiler_known_equality_path(&EqualFact::new_from_refs(&a, &b, default_line_file(),))
        .is_none());
}

#[test]
fn compiler_equality_evidence_merges_from_committed_child() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("compiler-equality-committed-child");
    let a: Obj = Identifier::new("a".to_string()).into();
    let b: Obj = Identifier::new("b".to_string()).into();
    let c: Obj = Identifier::new("c".to_string()).into();
    store_compiler_equality(&mut runtime, a.clone(), b.clone(), FactId::new(1));

    runtime
        .run_in_local_env_and_commit(|runtime| {
            store_compiler_equality(runtime, b.clone(), c.clone(), FactId::new(2));
            Ok(())
        })
        .expect("committed-child evidence probe should run");
    let path = runtime
        .compiler_known_equality_path(&EqualFact::new_from_refs(&a, &c, default_line_file()))
        .expect("committed child equality should remain visible");
    assert_eq!(path.len(), 2);
    assert_eq!(path[0].source_fact_id, FactId::new(1));
    assert_eq!(path[1].source_fact_id, FactId::new(2));
}
