use litex::litex_to_lean_compiler::compile_source;

fn compile_on_verifier_stack(source: &'static str, label: &'static str) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("compiler-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || compile_source(source, label))
        .expect("spawn compiler verifier thread")
        .join()
        .expect("compiler verifier thread panicked")
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
fn top_level_atomic_membership_emits_source_and_inferred_fact_ids() {
    let generated = compile_on_verifier_stack("1 $in N\n", "atomic_membership.lit")
        .expect("compile top-level atomic membership");
    assert!(generated.contains("Litex.In (1 : ℂ) Litex.N"));
    assert!(generated.contains("Litex.Rules.complexEqNatInN (1 : ℂ) 1 (by norm_num)"));
    assert!(generated.contains("Litex.Le (0 : ℂ) (1 : ℂ)"));
    assert!(generated.contains("Litex.OrderBridge.leOfComplexReals (by norm_num)"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn known_equality_paths_replay_same_symmetry_and_transitivity() {
    let generated = compile_on_verifier_stack(
        "forall a, b set:\n    a = b\n    =>:\n        b = a\n\nforall a, b, c set:\n    a = b\n    b = c\n    =>:\n        a = c\n",
        "known_equality.lit",
    )
    .expect("compile exact known-equality paths");
    assert!(generated.contains("Litex.Same.symm (__h0_3)"));
    assert!(generated.contains("Litex.Same.trans (__h1_4) (__h1_5)"));
    assert!(!generated.contains("Eq.symm"));
    assert!(!generated.contains("Eq.trans"));
}

#[test]
fn not_equal_symmetry_negates_heterogeneous_same() {
    let generated = compile_on_verifier_stack(
        "forall a, b set:\n    a != b\n    =>:\n        b != a\n",
        "not_equal_symmetry.lit",
    )
    .expect("compile not-equality symmetry");
    assert!(generated.contains("(__h0_3 : ¬ Litex.Same a b)"));
    assert!(generated.contains("¬ Litex.Same b a"));
    assert!(generated.contains("Litex.Rules.notSameSymm (__h0_3)"));
}

#[test]
fn conjunction_disjunction_and_alpha_forall_citations_replay_exact_evidence() {
    let generated = compile_on_verifier_stack(
        "1 = 1 and 2 = 2\n\nforall a, b set:\n    a = a\n    b = b\n    =>:\n        a = a and b = b\n\nforall a, b set:\n    a = a\n    =>:\n        a = a or b = b\n\nforall x, y set:\n    x = y\n    =>:\n        y = x\n\nforall a, b set:\n    a = b\n    =>:\n        b = a\n",
        "propositional_fact_spine.lit",
    )
    .expect("compile propositional proof spine");
    assert!(generated.contains("Litex.Same (1 : ℂ) (1 : ℂ) ∧ Litex.Same (2 : ℂ) (2 : ℂ)"));
    assert!(generated.contains("exact ⟨Litex.Same.refl (1 : ℂ), Litex.Same.refl (2 : ℂ)⟩"));
    assert!(generated.contains("exact ⟨__h1_3, __h1_4⟩"));
    assert!(generated.contains("exact Or.inl (__h2_3)"));
    assert!(generated.contains("theorem __fact4 :\n    ∀ (__p1 : Litex.Set) (__p2 : Litex.Set)"));
    assert!(generated.contains(":= __fact3"));
}

#[test]
fn conjunction_projection_replays_inferred_fact_ids() {
    let generated = compile_on_verifier_stack(
        "forall a, b, c, d set:\n    a != b and c != d\n    =>:\n        c != d\n",
        "conjunction_projection.lit",
    )
    .expect("compile conjunction projection proof spine");
    assert!(generated.contains("have __i0_0 : ¬ Litex.Same c d := (__h0_5).2"));
    assert!(generated.contains("exact __i0_0"));
}

#[test]
fn unary_function_set_application_consumes_both_memberships() {
    let generated = compile_on_verifier_stack(
        "forall s, S set, x s, f fn(y s) S:\n    f(x) = f(x)\n",
        "4_FunctionSet.lit",
    )
    .expect("compile unary function-set tracer");
    assert!(generated.contains("import Litex\n"));
    assert!(!generated.contains("import Litex.Rules\n"));
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
    let error = compile_on_verifier_stack("1 != 0\n", "unsupported.lit")
        .expect_err("unsupported fact must fail closed");
    assert!(error.contains("supports positive <, >, <=, or >= facts"));
}

#[test]
fn proof_scope_tracer_emits_named_theorem_claim_and_example() {
    let generated = compile_on_verifier_stack(
        "thm one_eq_one:\n    ? forall:\n        1 = 1\n\nclaim:\n    ? 2 = 2\n    2 = 2\n\nexample:\n    ? 3 = 3\n    3 = 3\n",
        "8_ProofScopes.lit",
    )
    .expect("compile proof-scope tracer");
    assert!(generated.contains("theorem one_eq_one :"));
    assert!(generated.contains("theorem __fact1 : Litex.Same (2 : ℂ) (2 : ℂ)"));
    assert!(generated.contains("example : Litex.Same (3 : ℂ) (3 : ℂ)"));
    assert!(generated.contains("have __step1 : Litex.Same (2 : ℂ) (2 : ℂ)"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn cases_and_contradiction_replay_branch_local_fact_ids() {
    let generated = compile_on_verifier_stack(
        "thm cases_and_contra:\n    ? forall:\n        2 = 2\n    by cases:\n        ? 1 = 1\n        case 1 = 1:\n            by contra:\n                ? 2 = 2\n                impossible 2 != 2\n",
        "9_CasesAndContradiction.lit",
    )
    .expect("compile cases-and-contradiction tracer");
    assert!(generated.contains("theorem cases_and_contra :"));
    assert!(generated.contains("have __case1"));
    assert!(generated.contains("by_contra __reverse"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn existential_intro_and_elim_use_native_carrier_and_exact_projections() {
    let generated = compile_on_verifier_stack(
        "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\ny = 1\n",
        "10_ExistentialWitness.lit",
    )
    .expect("compile existential introduction/elimination tracer");
    assert!(generated.contains("∃ (x : ℂ), Litex.In x Litex.R ∧ Litex.Same x (1 : ℂ)"));
    assert!(generated.contains("noncomputable def y : ℂ := Classical.choose"));
    assert!(generated.contains("Classical.choose_spec"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn object_definitions_emit_native_values_and_replay_definition_evidence() {
    let generated = compile_on_verifier_stack(
        "let x = 1\nx = 1\nhave y R = 1\ny $in R\ny = 1\nthm local_definition:\n    ? forall:\n        2 = 2\n    let z = 2\n    z = 2\n",
        "11_ObjectDefinitions.lit",
    )
    .expect("compile native object-definition tracer");
    assert!(generated.contains("noncomputable def x := (1 : ℂ)"));
    assert!(generated.contains("noncomputable def y := (1 : ℂ)"));
    assert!(generated.contains("Litex.In y Litex.R"));
    assert!(generated.contains("unfold x"));
    assert!(generated.contains("unfold y"));
    assert!(generated.contains("let z := (2 : ℂ)"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn multiple_existential_witnesses_fail_closed() {
    let error = compile_on_verifier_stack(
        "witness exist x, y R st {x = y} from 1, 1:\n    1 = 1\n",
        "unsupported_multi_witness.lit",
    )
    .expect_err("multiple witnesses must remain outside the reviewed compiler slice");
    assert!(
        error.contains("one positive witness and one body fact")
            || error.contains("one membership witness"),
        "unexpected error: {error}"
    );
}
