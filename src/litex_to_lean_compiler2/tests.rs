use litex::litex_to_lean_compiler2::compile_source;

fn compile_on_verifier_stack(source: &'static str, label: &'static str) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("compiler2-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || compile_source(source, label))
        .expect("spawn compiler2 verifier thread")
        .join()
        .expect("compiler2 verifier thread panicked")
}

#[test]
fn set_tracer_consumes_verified_equality_rewrite_ir() {
    let generated = compile_on_verifier_stack(
        "sketch:\n    have A set = R\n    have B set = C\n    forall a A, b B:\n        a = b\n        =>:\n            b $in A\n            a $in B\n    1 = 1\n",
        "1_SetSystem.lit",
    )
    .expect("compile set tracer");
    assert!(generated.contains("abbrev A : Litex.Set := Litex.R"));
    assert!(generated.contains("abbrev B : Litex.Set := Litex.C"));
    assert!(generated.contains("Litex.In.congr"));
    assert!(generated.contains("Litex.Same a b"));
    assert!(generated.contains("theorem __fact1 : Litex.Same (1 : ℂ) (1 : ℂ)"));
    assert!(generated.contains("namespace __Sketch01"));
    assert!(generated.contains("end __Sketch01"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn order_tracer_consumes_registered_rule_certificate() {
    let generated = compile_on_verifier_stack(
        "sketch:\n    forall a, b R:\n        a < b\n        =>:\n            a <= b\n",
        "2_OrderSystem.lit",
    )
    .expect("compile order tracer");
    assert!(generated.contains("Litex.Lt.toLe __h0_3"));
    assert!(generated.contains("Litex.Le a b"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn top_level_atomic_equality_reuses_verified_proof_ir() {
    let generated =
        compile_on_verifier_stack("1 = 1\n2 + 3 = 5\n2 + 3 = 5\n", "3_AtomicEquality.lit")
            .expect("compile top-level atomic equality tracer");
    assert!(generated.contains("Litex.Same.refl (1 : ℂ)"));
    assert!(generated.contains("Litex.Same ((2 : ℂ) + (3 : ℂ)) (5 : ℂ)"));
    assert!(generated.contains("have __wd1_0 : Litex.In (2 : ℂ) Litex.C"));
    assert!(generated.contains("Litex.Same.ofEq (by norm_num)"));
    assert!(generated.contains("theorem __fact2"));
    assert!(generated.contains("exact __fact1"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn unary_function_set_application_consumes_both_memberships() {
    let generated = compile_on_verifier_stack(
        "forall s, S set, x s, f fn(y s) S:\n    f(x) = f(x)\n",
        "4_FunctionSet.lit",
    )
    .expect("compile unary function-set tracer");
    assert!(generated.contains("(s : Litex.Set)"));
    assert!(generated.contains("(S : Litex.Set)"));
    assert!(generated.contains("Litex.In x s"));
    assert!(generated.contains("Litex.In f (Litex.fnSet s S)"));
    assert!(generated.contains("Litex.fnApply f __h0_4 x __h0_3"));
    assert!(!generated.contains("namespace __Sketch"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn sketch_compiles_to_an_isolated_namespace() {
    let generated =
        compile_on_verifier_stack("1 = 1\nsketch:\n    2 = 2\n3 = 3\n", "sketch_namespace.lit")
            .expect("compile sketch namespace tracer");
    assert!(generated.contains("namespace __Sketch01"));
    assert!(generated.contains("end __Sketch01"));
    assert_eq!(generated.matches("theorem __fact0").count(), 2);
    assert!(generated.contains("theorem __fact1 : Litex.Same (3 : ℂ) (3 : ℂ)"));
    assert!(!generated.contains("theorem __fact2"));
}

#[test]
fn function_application_without_domain_membership_is_rejected_by_litex() {
    let error = compile_on_verifier_stack(
        "forall s, S set, x S, f fn(y s) S:\n    f(x) = f(x)\n",
        "function_without_domain_membership.lit",
    )
    .expect_err("Litex must reject an application without x in s");
    assert!(
        error.contains("not in") || error.contains("well-defined") || error.contains("verify"),
        "unexpected error: {error}"
    );
}

#[test]
fn unsupported_atomic_predicate_fails_closed() {
    let error = compile_on_verifier_stack("1 < 2\n", "unsupported.lit")
        .expect_err("unsupported fact must fail closed");
    assert!(error.contains("atomic equality"));
}
