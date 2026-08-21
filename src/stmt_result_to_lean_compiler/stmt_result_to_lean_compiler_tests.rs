use litex::litex_to_lean_ir::capture_litex_to_lean_ir_from_source;
use litex::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source;
use litex::stmt_result_to_lean_compiler::{
    compile_litex_source_to_lean_source_rejecting_compatibility_adapter_for_audit,
    compile_litex_source_to_stmt_result_to_lean_compilation_report,
    StmtResultToLeanCompilationPhase, StmtResultToLeanCompilationStatus,
};

fn compile_on_verifier_stack(source: &'static str, label: &'static str) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("compiler-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || compile_litex_source_to_lean_source(source, label))
        .expect("spawn compiler verifier thread")
        .join()
        .expect("compiler verifier thread panicked")
}

fn compile_direct_result_only_on_verifier_stack(
    source: &'static str,
    label: &'static str,
) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("direct-result-compiler-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            compile_litex_source_to_lean_source_rejecting_compatibility_adapter_for_audit(
                source, label,
            )
        })
        .expect("spawn direct Result compiler verifier thread")
        .join()
        .expect("direct Result compiler verifier thread panicked")
}

fn capture_ir_debug_on_verifier_stack(
    source: &'static str,
    label: &'static str,
) -> Result<String, String> {
    std::thread::Builder::new()
        .name(format!("compiler-ir-test-{label}"))
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            capture_litex_to_lean_ir_from_source(source, label)
                .map(|ir| format!("{ir:#?}"))
                .map_err(|error| format!("{error:?}"))
        })
        .expect("spawn compiler IR verifier thread")
        .join()
        .expect("compiler IR verifier thread panicked")
}

#[test]
fn nonempty_set_witness_compiles_its_local_result_and_membership_evidence() {
    let generated = compile_direct_result_only_on_verifier_stack(
        "witness $is_nonempty_set({1, 2}) from 1:\n    do_nothing\n",
        "nonempty_set_witness_result.lit",
    )
    .expect("compile a nonempty-set witness from recursive Results");
    assert!(generated.contains("Litex.Set.Nonempty"), "{generated}");
    assert!(generated.contains("Litex.Set.coproduct"), "{generated}");
    assert!(generated.contains("__nonempty_witness"), "{generated}");
    assert!(generated.contains("Litex.Same.sumLeft"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn predicate_backed_witness_compiles_all_retained_fact_ids() {
    let generated = compile_on_verifier_stack(
        "prop has_copy(a R):\n    exist x R st {x = a}\nwitness $has_copy(2) from 2:\n    2 = 2\n",
        "predicate_backed_witness_result.lit",
    )
    .expect("compile a concrete-predicate witness from recursive Results");
    assert!(generated.contains("def has_copy"), "{generated}");
    assert!(generated.contains("unfold has_copy"), "{generated}");
    assert_eq!(
        generated.matches("theorem __fact").count(),
        3,
        "{generated}"
    );
    assert!(
        generated.contains("Litex.In (2 : ℂ) Litex.R"),
        "{generated}"
    );
    assert!(generated.contains("∃ (x : ℂ)"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn stored_forall_projections_replay_prior_conclusion_fact_ids() {
    let generated = compile_on_verifier_stack(
        "forall a C, f fn(x R) R:\n    a = 1\n    =>:\n        1 $in R\n        a $in R\n        f(a) = f(a)\n",
        "forall_projection_probe.lit",
    )
    .expect("compile independently stored forall projections");
    assert_eq!(
        generated.matches("theorem __fact").count(),
        3,
        "{generated}"
    );
    assert!(
        generated.contains("Litex.Rules.complexRealInR"),
        "{generated}"
    );
    assert!(generated.contains("Litex.In.congr"), "{generated}");
    assert!(generated.contains("Litex.fnApply"), "{generated}");
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn nested_forall_premises_replay_parameter_aliases_and_normalization() {
    let generated = compile_on_verifier_stack(
        "forall h fn(x R) R:\n    forall y R:\n        h(y) = h(y - 1)\n    =>:\n        h(2) = h(1)\n",
        "nested_forall_probe.lit",
    )
    .expect("compile a nested forall premise");
    assert!(generated.contains("(__domain1 : ∀"), "{generated}");
    assert!(generated.contains("convert (__domain1"), "{generated}");
    assert!(
        generated.contains("Litex.Rules.complexAddInR"),
        "{generated}"
    );
    assert!(!generated.contains("axiom "), "{generated}");
    assert!(!generated.contains("sorry"), "{generated}");
}

#[test]
fn compiler_core_keeps_representation_registry_closed() {
    let core = include_str!("../../lean/Litex/Core.lean");
    assert!(core.contains("private class PrimitiveRule"));
    assert!(core.contains("private class DerivedRule"));
    assert!(!core.contains("class BridgeRule"));
    assert!(!core.contains("def Bridge"));
    assert!(!core.contains("\naxiom "));
}

#[test]
fn compilation_report_is_transactional_and_marks_unsupported_result_routes() {
    let complete = compile_litex_source_to_stmt_result_to_lean_compilation_report(
        "1 = 1\n",
        "complete_report.lit",
    )
    .expect("capture and emit a complete report");
    assert_eq!(complete.status, StmtResultToLeanCompilationStatus::Complete);
    assert!(complete.is_complete());
    assert!(complete.unsupported.is_empty());
    assert!(complete.lean_code.contains("theorem __fact0"));

    let incomplete = compile_litex_source_to_stmt_result_to_lean_compilation_report(
        "1 != 0\n",
        "incomplete_report.lit",
    )
    .expect(
        "successful Result with an unsupported Lean-source construction route returns a report",
    );
    assert_eq!(
        incomplete.status,
        StmtResultToLeanCompilationStatus::Incomplete
    );
    assert!(!incomplete.is_complete());
    assert_eq!(incomplete.unsupported.len(), 1);
    assert_eq!(
        incomplete.unsupported[0].phase,
        StmtResultToLeanCompilationPhase::LeanSourceConstruction
    );
    assert!(incomplete
        .lean_code
        .contains("StmtResult-to-Lean compilation incomplete"));
    assert!(!incomplete.lean_code.contains("theorem __fact0"));
    assert!(!incomplete.lean_code.contains("axiom "));
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
        "sketch:\n    forall a, b R:\n        a < b\n        =>:\n            a <= b\n\n    forall a, b, c R:\n        a < b\n        b < c\n        =>:\n            a < c\n",
        "2_OrderSystem.lit",
    )
    .expect("compile order tracer");
    assert!(generated.contains("Litex.Lt.toLe (__domain1)"));
    assert!(generated.contains("Litex.In.rep a"));
    assert!(generated.contains("Litex.In.rep b"));
    assert!(generated.contains("Litex.Lt.trans (__domain1) (__domain2)"));
    assert!(generated.contains("Litex.In.rep c"));
    assert!(!generated.contains("RealCoherence"));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack(
        "sketch:\n    forall a, b C:\n        a < b\n        =>:\n            a <= b\n",
        "unsupported_complex_order.lit",
    )
    .expect_err("C-only order must remain outside the source ordered-real fragment");
    assert!(boundary.contains("ordered comparison requires both operands to belong to R"));
}

#[test]
fn top_level_atomic_equality_compiles_typed_result_evidence() {
    let generated =
        compile_on_verifier_stack("1 = 1\n2 + 3 = 5\n2 + 3 = 5\n", "3_AtomicEquality.lit")
            .expect("compile top-level atomic equality tracer");
    assert!(generated.contains("Litex.Same.refl (1 : ℂ)"));
    assert!(generated.contains("Litex.Same ((2 : ℂ) + (3 : ℂ)) (5 : ℂ)"));
    assert!(generated
        .contains("Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"));
    assert!(generated.contains("theorem __fact2"));
    assert!(generated.contains("exact __fact1"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn top_level_atomic_membership_emits_source_and_inferred_fact_ids() {
    let generated = compile_on_verifier_stack("2 + 3 $in N\n", "atomic_membership.lit")
        .expect("compile top-level atomic membership");
    assert!(generated.contains("Litex.In ((2 : ℂ) + (3 : ℂ)) Litex.N"));
    assert!(generated.contains("Litex.Rules.complexEqNatInN ((2 : ℂ) + (3 : ℂ)) 5 (by norm_num)"));
    assert!(generated.contains("Litex.Nonnegative ((2 : ℂ) + (3 : ℂ))"));
    assert!(generated.contains("Litex.Rules.nonnegativeOfInN (__fact0)"));
    assert!(!generated.contains("Litex.OrderBridge.nonnegativeOfComplexReal (by norm_num)"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn native_constants_use_mathlib_terms_and_exact_membership_rules() {
    const SOURCE: &str = "i = i\ne = e\npi = pi\n\ni $in C\ne $in R\npi $in R\ne $in C\npi $in C\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "19_NativeConstants.lit")
        .expect("capture native-constant tracer IR");
    for evidence in [
        "ImaginaryUnitInComplex",
        "EulerNumberInReal",
        "PiInReal",
        "StandardSetMembershipProjection",
    ] {
        assert!(ir.contains(evidence), "missing {evidence}: {ir}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "19_NativeConstants.lit")
        .expect("compile native-constant tracer");
    for term in ["Complex.I", "((Real.exp 1 : ℝ) : ℂ)", "((Real.pi : ℝ) : ℂ)"] {
        assert!(generated.contains(term), "missing {term}: {generated}");
    }
    for theorem in ["imaginaryUnitInC", "eInR", "piInR", "inCOfInR"] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack("1 $in Q+\n", "unsupported_one_in_q_pos.lit")
        .expect_err("other refined carriers need their own reviewed exact-carrier ABI");
    assert!(
        boundary.contains("has no supported Litex-to-Lean proof rule")
            || boundary.contains("unsupported standard set")
            || boundary.contains("Q+"),
        "unexpected boundary error: {boundary}"
    );
}

#[test]
fn standard_set_hierarchy_replays_exact_projection_chain() {
    const SOURCE: &str = "forall n N:\n    n $in Z\n\nforall n N:\n    n $in Q\n\nforall n N:\n    n $in R\n\nforall n N:\n    n $in C\n\nforall z Z:\n    z $in Q\n\nforall z Z:\n    z $in R\n\nforall z Z:\n    z $in C\n\nforall q Q:\n    q $in R\n\nforall q Q:\n    q $in C\n\nforall r R:\n    r $in C\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "16_StandardSetHierarchy.lit")
        .expect("capture standard-set hierarchy tracer IR");
    assert_eq!(
        ir.matches("StandardSetMembershipProjection").count(),
        10,
        "{ir}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "16_StandardSetHierarchy.lit")
        .expect("compile standard-set hierarchy tracer");
    for theorem in ["inZOfInN", "inQOfInZ", "inROfInQ", "inCOfInR"] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn positive_natural_uses_exact_subtype_and_projection() {
    const SOURCE: &str = "1 $in N+\n\nforall n N+:\n    n $in N\n";
    let core = include_str!("../../lean/Litex/Core.lean");
    assert!(core.contains("abbrev NPos : Litex.Set := setBuilder N (fun n => 0 < n)"));

    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "20_PositiveNaturalCarrier.lit")
        .expect("capture positive-natural tracer IR");
    assert!(ir.contains("ClosedNumericMembership"), "{ir}");
    assert!(ir.contains("StandardSetMembershipProjection"), "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "20_PositiveNaturalCarrier.lit")
        .expect("compile positive-natural tracer");
    for expected in [
        "Litex.In (1 : ℂ) Litex.NPos",
        "Litex.Rules.complexEqNatInNPos (1 : ℂ) 1 (by norm_num) (by norm_num)",
        "Litex.Rules.inNOfInNPos",
        "have __infer",
        "Litex.Rules.positiveOfInNPos (__h",
    ] {
        assert!(
            generated.contains(expected),
            "missing {expected}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack("1 $in Q+\n", "unsupported_one_in_q_pos.lit")
        .expect_err("other refined carriers must remain fail-closed");
    assert!(
        boundary.contains("has no supported Litex-to-Lean proof rule")
            || boundary.contains("unsupported standard set")
            || boundary.contains("Q+"),
        "unexpected boundary error: {boundary}"
    );
}

#[test]
fn positive_real_uses_exact_subtype_projection_and_elimination() {
    const SOURCE: &str =
        "1 $in R+\ne $in R+\npi $in R+\n\nforall r R+:\n    r $in R\n    r $in C\n    r > 0\n";
    let core = include_str!("../../lean/Litex/Core.lean");
    assert!(core.contains("abbrev RPos : Litex.Set := setBuilder R (fun r => 0 < r)"));

    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "21_PositiveRealCarrier.lit")
        .expect("capture positive-real tracer IR");
    for expected in [
        "ClosedNumericMembership",
        "EulerNumberInPositiveReal",
        "PiInPositiveReal",
        "StandardSetMembershipProjection",
        "PositiveRealMembership",
    ] {
        assert!(ir.contains(expected), "missing {expected}: {ir}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "21_PositiveRealCarrier.lit")
        .expect("compile positive-real tracer");
    for expected in [
        "Litex.Rules.complexEqRealInRPos (1 : ℂ) (1 : ℝ)",
        "Litex.Rules.eInRPos",
        "Litex.Rules.piInRPos",
        "Litex.Rules.inROfInRPos",
        "Litex.Rules.inCOfInR",
        "Litex.Rules.positiveOfInRPos",
        "have __infer",
        "Litex.Rules.positiveOfInRPos (__h",
    ] {
        assert!(
            generated.contains(expected),
            "missing {expected}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack(
        "forall r R:\n    r > 0\n    =>:\n        r $in R+\n",
        "unsupported_generic_r_pos_constructor.lit",
    )
    .expect_err("generic R+ construction still needs representative coherence");
    assert!(
        boundary.contains("refined numeric membership has no Lean replay adapter")
            || boundary.contains("has no supported Litex-to-Lean proof rule")
            || boundary.contains("R+"),
        "unexpected boundary error: {boundary}"
    );
}

#[test]
fn nonzero_numeric_carriers_replay_exact_constructors_and_widening() {
    const SOURCE: &str = include_str!("../../lean/examples/22_NonzeroNumericCarriers.lit");
    let core = include_str!("../../lean/Litex/Core.lean");
    for (carrier, base) in [
        ("ZStar", "Z"),
        ("QStar", "Q"),
        ("RStar", "R"),
        ("CStar", "C"),
    ] {
        assert!(
            core.contains(&format!("abbrev {carrier} : Litex.Set :="))
                && core.contains(&format!(
                    "setBuilder C (fun z => In z {base} ∧ ¬ Same z (0 : ℂ))"
                )),
            "missing exact {carrier} carrier"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "22_NonzeroNumericCarriers.lit")
        .expect("compile nonzero numeric-carrier tracer");
    for theorem in [
        "inZStarOfInZNotSameZero",
        "inQStarOfInQNotSameZero",
        "inRStarOfInRNotSameZero",
        "inCStarOfInCNotSameZero",
        "inZOfInZStar",
        "inQOfInQStar",
        "inROfInRStar",
        "inCOfInCStar",
        "inQStarOfInZStar",
        "inRStarOfInQStar",
        "inCStarOfInRStar",
        "notSameZeroOfInZStar",
        "notSameZeroOfInQStar",
        "notSameZeroOfInRStar",
        "notSameZeroOfInCStar",
    ] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(
        generated.contains(
            "(Litex.Rules.notSameZeroOfInCStar (__membership)) (Litex.Same.refl (0 : ℂ))"
        ),
        "closed C* nonmembership did not compile from its direct Result evidence: {generated}"
    );
    assert!(generated.contains("have __infer"), "{generated}");
    assert!(
        generated.contains("Litex.Rules.notSameZeroOfInZStar (__h")
            && generated.contains("Litex.Rules.notSameZeroOfInQStar (__h")
            && generated.contains("Litex.Rules.notSameZeroOfInRStar (__h")
            && generated.contains("Litex.Rules.notSameZeroOfInCStar (__h"),
        "nonzero inference did not stay inside its forall frames: {generated}"
    );
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack("1 $in Z*\n", "unsupported_closed_z_star.lit")
        .expect_err("standalone closed star reflection remains fail-closed");
    assert!(
        boundary.contains("closed comparison")
            || boundary.contains("unsupported inferred proof")
            || boundary.contains("has no supported Litex-to-Lean proof rule")
            || boundary.contains("Z*"),
        "unexpected boundary error: {boundary}"
    );
}

#[test]
fn numeric_carrier_closures_replay_exact_rules() {
    const SOURCE: &str = "forall a, b C:\n    a + b $in C\n\nforall a, b C:\n    a - b $in C\n\nforall a, b C:\n    a * b $in C\n\nforall a, b C:\n    b != 0\n    =>:\n        a / b $in C\n\nforall a, b Z:\n    a + b $in Z\n\nforall a, b Z:\n    a - b $in Z\n\nforall a, b Z:\n    a * b $in Z\n\nforall a, b Z:\n    b != 0\n    =>:\n        a % b $in Z\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "17_NumericCarrierClosures.lit")
        .expect("capture numeric carrier-closure tracer IR");
    assert_eq!(
        ir.matches("ComplexArithmeticMembershipClosure").count(),
        4,
        "{ir}"
    );
    assert_eq!(ir.matches("IntegerMembershipClosure").count(), 4, "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "17_NumericCarrierClosures.lit")
        .expect("compile numeric carrier-closure tracer");
    for theorem in [
        "complexAddInC",
        "complexSubInC",
        "complexMulInC",
        "complexDivInC",
        "complexAddInZ",
        "complexSubInZ",
        "complexMulInZ",
        "complexIntInZ",
    ] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
    assert!(
        generated.contains("Litex.In.rep a __h7_1")
            && generated.contains("Litex.In.rep b __h7_2")
            && generated.contains(" % "),
        "integer remainder did not consume its two exact visible representatives: {generated}"
    );
}

#[test]
fn rational_and_natural_carrier_closures_replay_exact_rules() {
    const SOURCE: &str = "forall a, b Q:\n    a + b $in Q\n\nforall a, b Q:\n    a - b $in Q\n\nforall a, b Q:\n    a * b $in Q\n\nforall a, b Q:\n    b != 0\n    =>:\n        a / b $in Q\n\nforall a, b N:\n    a + b $in N\n\nforall a, b N:\n    a * b $in N\n\nforall a Q, z Z:\n    a != 0\n    =>:\n        a^z $in Q\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "18_RationalNaturalClosures.lit")
        .expect("capture rational/natural carrier-closure tracer IR");
    assert_eq!(ir.matches("RationalMembershipClosure").count(), 5, "{ir}");
    assert_eq!(ir.matches("NaturalMembershipClosure").count(), 2, "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "18_RationalNaturalClosures.lit")
        .expect("compile rational/natural carrier-closure tracer");
    for theorem in [
        "complexAddInQ",
        "complexSubInQ",
        "complexMulInQ",
        "complexDivInQ",
        "complexAddInN",
        "complexMulInN",
    ] {
        assert!(
            generated.contains(&format!("Litex.Rules.{theorem}")),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
    assert_eq!(generated.matches("have __infer4_").count(), 2);
    assert_eq!(generated.matches("have __infer5_").count(), 2);
    assert!(generated.contains("Litex.Rules.nonnegativeOfInN (__h4_1)"));
    assert!(generated.contains("Litex.Rules.complexEqNatInN"));
    assert!(!generated.contains("complexAddInN (__h4_1)"));
    assert!(!generated.contains("complexMulInN (__h5_1)"));
    assert!(
        generated.contains("Litex.In.rep a __h6_1")
            && generated.contains("Litex.In.rep z __h6_2")
            && generated.contains("Litex.Rules.complexRatInQ")
            && generated.contains(" ^ "),
        "rational power did not consume its exact Q/Z representatives: {generated}"
    );
}

#[test]
fn known_equality_paths_replay_same_symmetry_and_transitivity() {
    const SOURCE: &str = "forall a, b set:\n    a = b\n    =>:\n        b = a\n\nforall a, b, c set:\n    a = b\n    b = c\n    =>:\n        a = c\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "known_equality.lit")
        .expect("capture exact known-equality paths");
    assert!(ir.contains("ForallIntroduction"));
    assert!(ir.contains("KnownEqualityPath"));
    assert!(ir.contains("KnownFactCitation"));
    assert!(!ir.contains("UseBuiltinStrategy"));

    let generated = compile_on_verifier_stack(SOURCE, "known_equality.lit")
        .expect("compile exact known-equality paths");
    assert!(generated.contains("Litex.Same.symm (__domain1)"));
    assert!(generated.contains("Litex.Same.trans (__domain1) (__domain2)"));
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
    assert!(generated.contains("(__domain1 : ¬ Litex.Same __p1 __p2)"));
    assert!(generated.contains("¬ Litex.Same b a"));
    assert!(generated.contains("Litex.Rules.notSameSymm (__domain1)"));
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
    assert!(generated
        .contains("have __c1_0 : Litex.Same a a ∧ Litex.Same b b := ⟨__domain1, __domain2⟩"));
    assert!(generated.contains("exact __c1_0"));
    assert!(
        generated.contains("have __c2_0 : Litex.Same a a ∨ Litex.Same b b := Or.inl (__domain1)")
    );
    assert!(generated.contains("exact __c2_0"));
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
    assert!(generated.contains("have __c0_0"));
    assert!(generated.contains(":= __i0_0"));
    assert!(generated.contains("exact __c0_0"));
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
    assert!(generated.contains("(__p1 : Litex.Set)"));
    assert!(generated.contains("(__p2 : Litex.Set)"));
    assert!(generated.contains("Litex.In __p3 __p1"), "{generated}");
    assert!(
        generated.contains("__type4 : Litex.In __p4 (Litex.fnSet"),
        "{generated}"
    );
    assert!(generated.contains("Litex.fnApply f __h0_4 x (__h0_3)"));
    assert!(!generated.contains("namespace __Sketch"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn multilayer_application_preserves_each_unary_source_contract() {
    const SOURCE: &str =
        "forall S, T, U set, a S, b T, g fn(x S) fn(y T) U:\n    g(a)(b) = g(a)(b)\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "23_MultilayerApplication.lit")
        .expect("capture multi-layer application tracer IR");
    assert!(ir.contains("through_layer_index: 0"), "{ir}");
    assert!(ir.contains("layer_index: 0"), "{ir}");
    assert!(ir.contains("layer_index: 1"), "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "23_MultilayerApplication.lit")
        .expect("compile multi-layer application tracer");
    assert!(generated.contains("Litex.In __p6 (Litex.fnSet"));
    assert!(generated.contains("let __fn_layer1 := (Litex.fnApply g __h0_6 a (__h0_4))"));
    assert!(generated.contains("Litex.fnApplyOwn __fn_layer1"));
    assert!(generated.contains("(Litex.In.own (Litex.fnSet"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));

    const THREE_LAYERS: &str = "forall S, T, U, V set, a S, b T, c U, g fn(x S) fn(y T) fn(z U) V:\n    g(a)(b)(c) = g(a)(b)(c)\n";
    let generated = compile_on_verifier_stack(THREE_LAYERS, "three_layer_application.lit")
        .expect("compile three source application layers");
    assert!(generated.contains("let __fn_layer2 :="));
    assert!(generated.contains("Litex.fnApplyOwn __fn_layer2"));
    assert!(generated.contains("(U : Litex.Set.{0}) (V : Litex.Set.{0})"));

    const SAME_LAYER: &str =
        "forall S, T, U set, a S, b T, f fn(x S, y T) U:\n    f(a, b) = f(a, b)\n";
    let same_layer_ir =
        capture_ir_debug_on_verifier_stack(SAME_LAYER, "23_MultilayerApplication.lit")
            .expect("capture same-layer telescope IR");
    assert!(same_layer_ir.contains("parameter_index: 0"));
    assert!(same_layer_ir.contains("parameter_index: 1"));
    let same_layer = compile_on_verifier_stack(SAME_LAYER, "23_MultilayerApplication.lit")
        .expect("compile one exact two-parameter source layer");
    assert!(same_layer.contains("Litex.fnTelescopeSet"));
    assert!(same_layer.contains("Litex.FnTelescope.parameter"));
    assert!(same_layer.contains("Litex.fnTelescopeApply f"));
    assert!(same_layer.contains(").down"));
    assert!(!same_layer.contains("Litex.Object"));
    assert!(!same_layer.contains("sorry"));

    const SAME_LAYER_DOMAIN: &str = "forall f fn(x, y R: x > 0, y > 0) R, a, b R:\n    a > 0\n    b > 0\n    =>:\n        f(a, b) = f(a, b)\n";
    let same_layer_domain =
        compile_on_verifier_stack(SAME_LAYER_DOMAIN, "23_MultilayerApplication.lit")
            .expect("compile same-layer ordered domain clauses");
    assert!(same_layer_domain.contains("Litex.FnTelescope.requirement"));
    assert!(same_layer_domain.contains("Litex.Positive __arg1"));
    assert!(same_layer_domain.contains("Litex.Positive __arg2"));
    assert!(same_layer_domain.contains("__h0_4"));
    assert!(same_layer_domain.contains("__h0_5"));

    let split = compile_on_verifier_stack(
        "forall S, T, U set, a S, b T, f fn(x S, y T) U:\n    f(a)(b) = f(a)(b)\n",
        "split_same_layer_application.lit",
    )
    .expect_err("a source layer must not be repaired by target currying");
    assert!(
        split.contains("parameter")
            || split.contains("well-defined")
            || split.contains("cannot verify"),
        "unexpected split-layer error: {split}"
    );
}

#[test]
fn dependent_function_sets_keep_parameter_and_return_carriers() {
    const DEPENDENT_PARAMETER: &str = "forall f fn(x R, y {z R: z > x}) R:\n    f = f\n";
    let parameter =
        compile_on_verifier_stack(DEPENDENT_PARAMETER, "24_DependentAnonymousFunction.lit")
            .expect("compile a parameter set depending on an earlier source parameter");
    assert!(parameter.contains("Litex.fnTelescopeSet"), "{parameter}");
    assert!(
        parameter.contains("Litex.In.rep __arg1 __arg1_in"),
        "{parameter}"
    );
    assert!(parameter.contains("Litex.Lt"), "{parameter}");

    const DEPENDENT_RETURN: &str = "forall f fn(x R) {z R: z > x}, a R:\n    f(a) = f(a)\n";
    let returned = compile_on_verifier_stack(DEPENDENT_RETURN, "24_DependentAnonymousFunction.lit")
        .expect("compile an application with an argument-indexed exact return set");
    assert!(returned.contains("Litex.fnTelescopeSet"), "{returned}");
    assert!(returned.contains("Litex.fnTelescopeApply f"), "{returned}");
    assert!(returned.contains("Litex.setBuilder Litex.R"), "{returned}");
    assert!(returned.contains(").down"), "{returned}");
    assert!(!returned.contains("Litex.Object"));
    assert!(!returned.contains("sorry"));
}

#[test]
fn compound_anonymous_functions_replay_their_owned_wd_scope() {
    const SOURCE: &str = "fn(x R) R {x + 1} = fn(y R) R {y + 1}\n\nforall a R:\n    fn(x R) R {x + 1}(a) = fn(x R) R {x + 1}(a)\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "24_DependentAnonymousFunction.lit")
        .expect("capture compound anonymous-function WD IR");
    assert!(ir.contains("AnonymousFunctionBodyMembership"), "{ir}");
    assert!(ir.contains("owned_binder_scope_id: Some"), "{ir}");
    assert!(ir.contains("FunctionHead"), "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "24_DependentAnonymousFunction.lit")
        .expect("compile compound anonymous values and their direct application");
    assert!(
        generated.contains("Litex.Rules.complexAddInR"),
        "{generated}"
    );
    assert!(generated.contains("Litex.fnApplyOwn"), "{generated}");
    assert!(
        generated.contains("Litex.In.own (Litex.fnSet"),
        "{generated}"
    );
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));

    let boundary = compile_on_verifier_stack(
        "fn(x R) N {x} = fn(y R) N {y}\n",
        "unsupported_anonymous_return.lit",
    )
    .expect_err("an anonymous body without checked return membership must be rejected");
    assert!(boundary.contains("not verified to belong to declared return set"));
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
    assert!(error.contains(
        "closed comparison requires an order relation; closed equality and disequality use separate semantic adapters"
    ));
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
fn structured_and_nested_case_scopes_compile_recursive_result_fields() {
    const STRUCTURED: &str = "by cases:\n    ? 2 = 2\n    case 1 = 1 and 2 = 2:\n        1 = 1\nby contra:\n    ? not 2 < 1\n    impossible 2 < 1\n";
    let structured = compile_on_verifier_stack(STRUCTURED, "9_CasesAndContradiction.lit")
        .expect("compile conjunction assumptions and a negative contradiction goal");
    assert!(
        structured.contains("have __case1_component1"),
        "{structured}"
    );
    assert!(
        structured.contains("have __case1_component2"),
        "{structured}"
    );
    assert!(
        structured.contains("Classical.byContradiction"),
        "{structured}"
    );

    const NESTED: &str = "have fn identity(x R) R = x\nby cases:\n    ? identity(1) = identity(1)\n    case 1 = 1:\n        by contra:\n            ? 2 = 2\n            impossible 2 != 2\n        1 $in R\nby contra:\n    ? 3 = 3\n    by cases:\n        ? 4 = 4\n        case 4 = 4:\n            5 = 5\n    impossible 3 != 3\n";
    let nested = compile_on_verifier_stack(NESTED, "nested_case_scope.lit")
        .expect("compile nested case/contradiction scopes with branch-local WD");
    assert!(
        nested.matches("by_contra __reverse").count() >= 2,
        "{nested}"
    );
    assert!(nested.contains("Litex.fnApplyOwn identity"), "{nested}");
    assert!(!nested.contains("sorry"));

    let reused = compile_on_verifier_stack(
        "2 = 2\nby contra:\n    ? 2 = 2\n    impossible 2 != 2\n",
        "reused_by_contra_goal.lit",
    )
    .expect("compile an explicit proof whose already-known goal receives no new FactId");
    assert_eq!(reused.matches("theorem __fact").count(), 1, "{reused}");
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
fn existential_elimination_statement_adapters_share_recursive_result_compilation() {
    let generated_from_object_definition = compile_on_verifier_stack(
        "witness exist x R st {x = 1} from 1:\n    1 = 1\nhave selected R:\n    selected = 1\nselected = 1\n",
        "object_by_existential_elimination_adapter.lit",
    )
    .expect("compile the direct object-by-existential Result adapter");
    assert!(
        generated_from_object_definition.contains("noncomputable def selected"),
        "{generated_from_object_definition}"
    );
    assert!(generated_from_object_definition.contains("Classical.choose_spec"));
    assert!(!generated_from_object_definition.contains("sorry"));

    let generated_from_predicate = compile_on_verifier_stack(
        "prop has_copy(a R):\n    exist x R st {x = a}\nwitness exist x R st {x = 2} from 2:\n    2 = 2\nby def $has_copy(2)\nobtain copy from $has_copy(2)\ncopy = 2\n",
        "predicate_backed_existential_elimination_adapter.lit",
    )
    .expect("compile the direct predicate-backed obtain Result adapter");
    assert!(
        generated_from_predicate.contains("noncomputable def copy"),
        "{generated_from_predicate}"
    );
    assert!(generated_from_predicate.contains("unfold has_copy at __definition"));
    assert!(generated_from_predicate.contains("Classical.choose_spec"));
    assert!(!generated_from_predicate.contains("Litex.Object"));
    assert!(!generated_from_predicate.contains("LitexObject"));
    assert!(!generated_from_predicate.contains("sorry"));

    let generated_from_theorem = compile_on_verifier_stack(
        "thm self_exists:\n    ? forall a R:\n        exist x R st {x = a}\n    witness exist x R st {x = a} from a:\n        a = a\nobtain theorem_copy from thm self_exists(3)\n",
        "theorem_backed_existential_elimination_adapter.lit",
    )
    .expect("compile the direct theorem-backed obtain Result adapter");
    assert!(
        generated_from_theorem.contains("noncomputable def theorem_copy"),
        "{generated_from_theorem}"
    );
    assert!(generated_from_theorem.contains("self_exists (3 : ℂ)"));
    assert!(generated_from_theorem.contains("Classical.choose_spec"));
    assert!(!generated_from_theorem.contains("Litex.Object"));
    assert!(!generated_from_theorem.contains("LitexObject"));
    assert!(!generated_from_theorem.contains("sorry"));
}

#[test]
fn object_definitions_emit_native_values_and_replay_definition_evidence() {
    let generated = compile_direct_result_only_on_verifier_stack(
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
fn named_real_functions_compile_compound_bodies_and_domain_clauses() {
    let generated = compile_direct_result_only_on_verifier_stack(
        "have fn id(x R) R = x\nid(1) = 1\nhave fn inc(x R) R = x + 1\ninc(1) = 1 + 1\nhave fn reciprocal(x R: x != 0) R = 1 / x\nforall a R:\n    a != 0\n    =>:\n        reciprocal(a) = 1 / a\nhave fn into_builder(x R) {z R: z = z} = x\ninto_builder(1) = 1\n",
        "12_NamedFunction.lit",
    )
    .expect("compile compound named-function tracer");
    assert!(generated.contains("noncomputable def id : Litex.Fn Litex.R Litex.R"));
    assert!(generated.contains("Litex.In id (Litex.fnSet Litex.R Litex.R)"));
    assert!(generated.contains("Litex.fnApplyOwn id __fact0"));
    assert!(generated.contains("Litex.In.same_rep (1 : ℂ)"));
    assert!(generated.contains("noncomputable def inc : Litex.Fn Litex.R Litex.R"));
    assert!(generated.contains("Litex.Same.realAddComplex"));
    assert!(generated.contains("noncomputable def reciprocal : Litex.FnWhere"));
    assert!(generated.contains("Litex.fnSetWhere Litex.R Litex.R"));
    assert!(generated.contains("Litex.fnApplyWhereOwn reciprocal"));
    assert!(generated.contains("Litex.Same.realDivComplex"));
    assert!(generated.contains("Litex.Same.realComplex ((Litex.In.rep a "));
    assert!(!generated.contains("Litex.Same.symm (Litex.In.same_rep a (__h8_1))"));
    assert!(generated.contains("noncomputable def into_builder : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.setBuilder Litex.R"));
    assert!(generated.contains("Litex.Rules.inSetBuilder"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn into_builder"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn concrete_predicate_definition_and_by_def_replay_checked_components() {
    let generated = compile_on_verifier_stack(
        "prop is_unit_pair(x R, y R):\n    x = 1\n    y = 1\n\n1 = 1\nby def $is_unit_pair(1, 1)\n",
        "13_PredicateDefinitions.lit",
    )
    .expect("compile concrete predicate tracer");
    assert!(generated.contains("def is_unit_pair"));
    assert!(generated.contains("Litex.In x Litex.R ∧ Litex.In y Litex.R"));
    assert!(generated.contains("unfold is_unit_pair"));
    assert!(generated.contains(
        "exact ⟨Litex.Rules.complexRealInR (1 : ℝ), Litex.Rules.complexRealInR (1 : ℝ), __fact0, __fact0⟩"
    ));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn abstract_predicate_and_explicit_trust_emit_only_source_axioms() {
    const SOURCE: &str = "abstract_prop marked(x)\n\ntrust $marked(1)\n\n$marked(1)\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "25_ExplicitSourceAxioms.lit")
        .expect("capture abstract-predicate and explicit-trust IR");
    assert!(ir.contains("DefAbstractPropStmt"), "{ir}");
    assert_eq!(ir.matches("Trusted").count(), 1, "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "25_ExplicitSourceAxioms.lit")
        .expect("compile exact source-scoped axiom declarations");
    assert_eq!(generated.matches("axiom ").count(), 2, "{generated}");
    assert!(generated.contains("axiom marked"), "{generated}");
    assert!(
        generated.contains("axiom __fact0 : marked (1 : ℂ)"),
        "{generated}"
    );
    assert!(
        generated.contains("theorem __fact1 : marked (1 : ℂ)"),
        "{generated}"
    );
    assert!(generated.contains("exact __fact0"), "{generated}");
    assert!(!generated.contains("sorry"));

    let ordinary = compile_on_verifier_stack("1 = 1\n", "ordinary_no_axiom.lit")
        .expect("compile an ordinary checked statement without an axiom");
    assert_eq!(ordinary.matches("axiom ").count(), 0, "{ordinary}");

    let unproved = compile_on_verifier_stack(
        "abstract_prop unproved(x)\n\n$unproved(1)\n",
        "unproved_abstract_predicate.lit",
    )
    .expect_err("an abstract interface declaration must not prove an application");
    assert!(
        unproved.contains("verification failed") || unproved.contains("unknown result"),
        "{unproved}"
    );
}

#[test]
fn set_builder_membership_and_nonempty_choice_use_exact_carriers() {
    let generated = compile_on_verifier_stack(
        "have S set = {x R: x = x}\nS = S\n1 $in {x R: x = 1}\nprop is_one(x R):\n    x = 1\n1 = 1\nby def $is_one(1)\n1 $in {x R: $is_one(x)}\nhave chosen R\nchosen $in R\n",
        "14_SetBuilderAndChoice.lit",
    )
    .expect("compile set-builder and choice tracer");
    assert!(generated.contains("Litex.setBuilder Litex.R"));
    assert!(generated.contains("Litex.Rules.inSetBuilder"));
    assert!(generated.contains("Litex.Rules.inBaseOfInSetBuilder"));
    assert!(generated.contains("Litex.Same.trans (Litex.Same.symm"));
    assert!(generated.contains("rcases Litex.Rules.inSetBuilder_iff.mp"));
    assert!(generated.contains("unfold is_one at __selected"));
    assert!(generated.contains("noncomputable def chosen : Litex.R.Carrier"));
    assert!(generated.contains("Litex.In.own Litex.R chosen"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn builtin_strategy_ir_marks_each_selected_layer_and_replays_exact_rules() {
    const SOURCE: &str = "forall a, b, c, d R:\n    a > 0\n    b >= 0\n    c >= 0\n    d >= 0\n    =>:\n        (a + b) + (c + d) > 0\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("capture builtin-strategy tracer IR");
    assert_eq!(ir.matches("UseBuiltinStrategy").count(), 1, "{ir}");
    assert_eq!(ir.matches("AddPositiveLeftStrict").count(), 1, "{ir}");
    assert_eq!(
        ir.matches("order.add_positive_of_positive_nonnegative")
            .count(),
        1,
        "{ir}"
    );
    assert_eq!(ir.matches("order.add_nonnegative").count(), 1, "{ir}");
    assert!(ir.matches("KnownFactCitation").count() >= 4, "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile builtin-strategy tracer");
    assert_eq!(
        generated
            .matches("Litex.Rules.complexAddPositiveLeftStrict")
            .count(),
        2
    );
    assert_eq!(
        generated
            .matches("Litex.Rules.complexAddNonnegative")
            .count(),
        1
    );
    assert!(generated.contains("Litex.Positive.congr (Litex.Same.trans"));
    assert!(generated.contains("Litex.Nonnegative.congr (Litex.Same.trans"));
    assert!(generated.contains("Litex.In.same_rep a"));
    assert!(generated.contains("Litex.Same.realComplex (Litex.In.rep a"));
    assert!(!generated.contains("UseBuiltinStrategy"));
    assert!(!generated.contains("sorry"));

    const REAL_ADDITION_CARRIER_SOURCE: &str = "forall a, b R:\n    a + b $in R\n";
    let carrier_ir =
        capture_ir_debug_on_verifier_stack(REAL_ADDITION_CARRIER_SOURCE, "15_BuiltinStrategy.lit")
            .expect("capture real-addition carrier tracer IR");
    assert_eq!(
        carrier_ir
            .matches("RealArithmeticMembershipClosure")
            .count(),
        1,
        "{carrier_ir}"
    );
    let carrier_generated =
        compile_on_verifier_stack(REAL_ADDITION_CARRIER_SOURCE, "15_BuiltinStrategy.lit")
            .expect("compile real-addition carrier tracer");
    assert!(carrier_generated.contains("Litex.Rules.complexAddInR"));
    assert!(carrier_generated.contains("Litex.Rules.complexRealInR ((Litex.In.rep a"));
    assert!(carrier_generated.contains("Litex.Rules.complexRealInR ((Litex.In.rep b"));

    const RIGHT_STRICT_SOURCE: &str = "forall a, b, c, d R:\n    a >= 0\n    b >= 0\n    c >= 0\n    d > 0\n    =>:\n        (a + b) + (c + d) > 0\n";
    let right_ir =
        capture_ir_debug_on_verifier_stack(RIGHT_STRICT_SOURCE, "15_BuiltinStrategy.lit")
            .expect("capture right-strict builtin-strategy tracer IR");
    assert_eq!(
        right_ir.matches("AddPositiveRightStrict").count(),
        1,
        "{right_ir}"
    );
    assert_eq!(
        right_ir
            .matches("order.add_positive_of_nonnegative_positive")
            .count(),
        1,
        "{right_ir}"
    );

    let right_generated = compile_on_verifier_stack(RIGHT_STRICT_SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile right-strict builtin-strategy tracer");
    assert_eq!(
        right_generated
            .matches("Litex.Rules.complexAddPositiveRightStrict")
            .count(),
        2
    );
    assert!(!right_generated.contains("Litex.Object"));
    assert!(!right_generated.contains("Set.univ"));
    assert!(!right_generated.contains("axiom "));
    assert!(!right_generated.contains("sorry"));
}

#[test]
fn real_arithmetic_membership_closures_replay_exact_rules() {
    const SOURCE: &str = "forall a, b R:\n    a + b $in R\n\nforall a, b R:\n    a - b $in R\n\nforall a, b R:\n    a * b $in R\n\nforall a, b R:\n    b != 0\n    =>:\n        a / b $in R\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("capture real arithmetic closure tracer IR");
    assert!(
        ir.matches("RealArithmeticMembershipClosure").count() >= 4,
        "{ir}"
    );

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile real arithmetic closure tracer");
    for theorem in [
        "Litex.Rules.complexAddInR",
        "Litex.Rules.complexSubInR",
        "Litex.Rules.complexMulInR",
        "Litex.Rules.complexDivInR",
    ] {
        assert!(
            generated.contains(theorem),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn multiplicative_strategy_replays_canonical_mathlib_order_evidence() {
    const SOURCE: &str = "forall a, b, c, d R:\n    a >= 0\n    b >= 0\n    c >= 0\n    d >= 0\n    =>:\n        (a * b) * (c * d) >= 0\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("capture nested multiplicative strategy IR");
    assert!(ir.contains("UseBuiltinStrategy"), "{ir}");
    assert!(ir.contains("MulNonnegative"), "{ir}");
    assert!(ir.contains("order.mul_nonnegative"), "{ir}");

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile nested multiplicative signs through canonical zero order");
    assert_eq!(
        generated
            .matches("Litex.Rules.complexMulNonnegative")
            .count(),
        3,
        "{generated}"
    );
    assert!(generated.contains("Litex.Nonnegative"));
    assert!(!generated.contains("RealCoherence"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn direct_multiplicative_and_divisive_sign_rules_all_compile() {
    const SOURCE: &str = "forall a, b R:\n    a >= 0\n    b >= 0\n    =>:\n        a * b >= 0\n\nforall a, b R:\n    a > 0\n    b > 0\n    =>:\n        a * b > 0\n\nforall a, b R:\n    a >= 0\n    b > 0\n    =>:\n        a / b >= 0\n\nforall a, b R:\n    a > 0\n    b > 0\n    =>:\n        a / b > 0\n";
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("capture direct multiplication/division sign IR");
    for rule in [
        "MulNonnegative",
        "MulPositive",
        "DivNonnegative",
        "DivPositive",
    ] {
        assert!(ir.contains(rule), "missing {rule}: {ir}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "15_BuiltinStrategy.lit")
        .expect("compile direct multiplication/division sign rules");
    for theorem in [
        "Litex.Rules.complexMulNonnegative",
        "Litex.Rules.complexMulPositive",
        "Litex.Rules.complexDivNonnegative",
        "Litex.Rules.complexDivPositive",
    ] {
        assert!(
            generated.contains(theorem),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("RealCoherence"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn unsupported_subtractive_strategy_rule_remains_fail_closed() {
    let error = compile_on_verifier_stack(
        "forall a, b R:\n    a <= b\n    =>:\n        b - a >= 0\n",
        "unsupported_builtin_strategy_rule.lit",
    )
    .expect_err("unreviewed subtractive sign rule must remain outside the compiler slice");
    assert!(
        error.contains("SubNonnegativeFromLessEqual"),
        "unexpected error: {error}"
    );
}

#[test]
fn nested_set_builder_binder_expression_remains_fail_closed() {
    let error = compile_on_verifier_stack(
        "2 $in {x R: x + 1 = 3}\n",
        "unsupported_nested_set_builder_transport.lit",
    )
    .expect_err("nested predicate transport must remain outside the reviewed adapter");
    assert!(
        error.contains("whole equality side") || error.contains("set-builder"),
        "unexpected error: {error}"
    );
}

#[test]
fn multi_parameter_named_function_uses_the_same_telescope_contract() {
    let generated = compile_on_verifier_stack(
        "have fn first(x, y R) R = x\nfirst(1, 1) = 1\n",
        "multi_parameter_function.lit",
    )
    .expect("compile a named two-parameter telescope function");
    assert!(generated.contains("noncomputable def first : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.fnTelescopeSet"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn first"));
    assert!(generated.contains("ULift.up"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("sorry"));
}

#[test]
fn indexed_tuple_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str = include_str!("../../lean/examples/29_IndexedTupleCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "29_IndexedTupleCompilerEnvironment.lit")
        .expect("compile indexed tuple from its recursive statement Result");
    assert!(generated.contains("noncomputable def coordinates : Litex.IndexedTuple 3 ℂ"));
    assert!(generated.contains("fun __index"));
    assert!(generated.contains("Litex.IsTuple coordinates"));
    assert!(generated.contains("Litex.tupleDim coordinates"));
    assert!(generated.contains("Litex.indexedTupleAt coordinates"));
    assert!(!generated.contains("LitexToLeanHaveTupleStmtIr"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn indexed_sequence_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str =
        include_str!("../../lean/examples/30_IndexedSequenceCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "30_IndexedSequenceCompilerEnvironment.lit")
        .expect("compile indexed sequence from its recursive statement Result");
    assert!(generated.contains("noncomputable def shifted_sequence : Litex.Fn Litex.NPos Litex.R"));
    assert!(generated.contains("Litex.sequenceSet Litex.R"));
    assert!(generated.contains("Litex.fnSet Litex.NPos Litex.R"));
    assert!(generated.contains("Litex.In.rep __arg __arg_in"));
    assert!(generated.contains("Litex.fnApplyOwn shifted_sequence"));
    assert!(!generated.contains("LitexToLeanHaveSeqStmtIr"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn finite_sequence_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str =
        include_str!("../../lean/examples/31_FiniteSequenceCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "31_FiniteSequenceCompilerEnvironment.lit")
        .expect("compile finite sequence from its recursive statement Result");
    assert!(generated.contains("noncomputable def bounded_sequence : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.finiteSequenceSet.{0} Litex.R (3 : Nat)"));
    assert!(generated.contains("Litex.FnTelescope.requirement"));
    assert!(generated.contains("fun __arg_domain => ULift.up"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn bounded_sequence"));
    assert!(!generated.contains("LitexToLeanHaveFiniteSeqStmtIr"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn matrix_definition_uses_the_recursive_result_environment() {
    const SOURCE: &str = include_str!("../../lean/examples/32_MatrixCompilerEnvironment.lit");
    let generated = compile_on_verifier_stack(SOURCE, "32_MatrixCompilerEnvironment.lit")
        .expect("compile matrix from its recursive statement Result");
    assert!(generated.contains("noncomputable def entry_matrix : Litex.FnTelescope.Carrier"));
    assert!(generated.contains("Litex.matrixSet.{0} Litex.R (2 : Nat) (3 : Nat)"));
    assert!(generated.contains("Litex.positiveNaturalParameterLessEqualNaturalBound __arg1"));
    assert!(generated.contains("Litex.positiveNaturalParameterLessEqualNaturalBound __arg2"));
    assert!(generated.contains("fun __arg_domain => ULift.up"));
    assert!(generated.contains("Litex.fnTelescopeApplyOwn (@entry_matrix)"));
    assert!(!generated.contains("LitexToLeanHaveMatrixStmtIr"));
    assert!(!generated.contains("axiom "));
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

#[test]
fn collections_and_aggregates_use_exact_typed_carriers() {
    const SOURCE: &str = include_str!("../../lean/examples/26_CollectionsAndAggregates.lit");
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "26_CollectionsAndAggregates.lit")
        .expect("capture collection and aggregate tracer IR");
    for evidence in ["FiniteSet(", "ListSetMembership", "TupleLiteralShape"] {
        assert!(
            ir.contains(evidence),
            "missing collection evidence {evidence}"
        );
    }

    let generated = compile_on_verifier_stack(SOURCE, "26_CollectionsAndAggregates.lit")
        .expect("compile typed collection and aggregate tracer");
    for term in [
        "Litex.Set.coproduct",
        "Litex.SingletonCarrier.element",
        "Litex.generalCart",
        "Litex.FnTelescope.Carrier",
        "Litex.closedRange",
        "Litex.SequenceLiteral.mk",
    ] {
        assert!(
            generated.contains(term),
            "missing generated collection term {term}"
        );
    }
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn set_operators_replay_registered_certificates_through_exact_carriers() {
    const SOURCE: &str = include_str!("../../lean/examples/27_SetOperators.lit");
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "27_SetOperators.lit")
        .expect("capture set-operator tracer IR");
    for rule in [
        "set.union_commutative",
        "set.union_associative",
        "set.intersect_commutative",
        "set.intersect_associative",
        "set.set_minus_membership",
    ] {
        assert!(ir.contains(rule), "missing {rule}: {ir}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "27_SetOperators.lit")
        .expect("compile exact set operators and registered rules");
    for theorem in [
        "Litex.SetRules.unionCommutative",
        "Litex.SetRules.unionAssociative",
        "Litex.SetRules.intersectCommutative",
        "Litex.SetRules.intersectAssociative",
        "Litex.SetRules.inSetMinus",
    ] {
        assert!(
            generated.contains(theorem),
            "missing {theorem}: {generated}"
        );
    }
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}

#[test]
fn extended_set_rules_use_exact_power_set_and_subset_certificates() {
    const SOURCE: &str = include_str!("../../lean/examples/28_ExtendedSetRules.lit");
    let ir = capture_ir_debug_on_verifier_stack(SOURCE, "28_ExtendedSetRules.lit")
        .expect("capture extended set-rule certificates");
    for rule in [
        "set.empty_subset",
        "set.union_finite",
        "set.intersect_finite",
        "set.power_set_membership_of_subset",
        "set.power_set_finite",
        "set.set_minus_union_de_morgan",
    ] {
        assert!(ir.contains(rule), "missing registered certificate {rule}");
    }

    let generated = compile_on_verifier_stack(SOURCE, "28_ExtendedSetRules.lit")
        .expect("compile extended exact-carrier set rules");
    for theorem in [
        "Litex.SetRules.emptySubset",
        "Litex.SetRules.unionFinite",
        "Litex.SetRules.intersectFinite",
        "Litex.SetRules.inPowerSetOfSubset",
        "Litex.SetRules.powerSetFinite",
        "Litex.SetRules.setMinusUnionDeMorgan",
    ] {
        assert!(
            generated.contains(theorem),
            "missing generated theorem {theorem}"
        );
    }
    assert!(!generated.contains("LitexObject"));
    assert!(!generated.contains("Litex.Object"));
    assert!(!generated.contains("Set.univ"));
    assert!(!generated.contains("axiom "));
    assert!(!generated.contains("sorry"));
}
